use num_traits::{One, Zero};
use stwo_prover::constraint_framework::TraceLocationAllocator;
use stwo_prover::constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval};
use stwo_prover::core::backend::simd::column::BaseColumn;
use stwo_prover::core::backend::simd::SimdBackend;
use stwo_prover::core::channel::Blake2sChannel;
use stwo_prover::core::fields::m31::BaseField;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::pcs::CommitmentSchemeProver;
use stwo_prover::core::pcs::PcsConfig;
use stwo_prover::core::poly::circle::CanonicCoset;
use stwo_prover::core::poly::circle::CircleEvaluation;
use stwo_prover::core::poly::circle::PolyOps;
use stwo_prover::core::poly::BitReversedOrder;
use stwo_prover::core::prover::prove;
use stwo_prover::core::prover::StarkProof;
use stwo_prover::core::vcs::blake2_merkle::Blake2sMerkleChannel;
use stwo_prover::core::vcs::blake2_merkle::Blake2sMerkleHasher;
use stwo_prover::core::ColumnVec;

pub fn store_u64(value: u64) -> (u32, u32) {
    let lower = value as u32;
    let upper = (value >> 32) as u32;
    (lower, upper)
}

pub fn reconstruct_u64(lower: u32, upper: u32) -> u64 {
    ((upper as u64) << 32) | (lower as u64)
}

pub struct LimbsProof {
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
    pub component: FrameworkComponent<LimbsEval>,
}

#[derive(Clone)]
pub struct LimbsEval {
    pub log_n_rows: u32,
}

pub type LimbsComponent = FrameworkComponent<LimbsEval>;

impl FrameworkEval for LimbsEval {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + 1
    }

    // input => (limb0, limb1)
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let limb0 = eval.next_trace_mask(); // low 32 bit
        let limb1 = eval.next_trace_mask(); // high 32 bit
        let low_limb0 = eval.next_trace_mask(); // Lower 32 bits of low bound
        let low_limb1 = eval.next_trace_mask(); // Upper 32 bits of low bound
        let is_greater = eval.next_trace_mask(); // Boolean flag for result

        // First compare high limbs
        let high_diff = eval.next_trace_mask();
        eval.add_constraint(high_diff.clone() - (limb1.clone() - low_limb1.clone()));

        // Then compare low limbs if high limbs are equal
        let low_diff = eval.next_trace_mask();
        eval.add_constraint(low_diff.clone() - (limb0.clone() - low_limb0.clone()));

        // Ensure is_greater is boolean
        eval.add_constraint(is_greater.clone() * (E::F::one() - is_greater.clone()));

        // If high_diff > 0, is_greater must be 1
        eval.add_constraint(high_diff.clone() * (is_greater.clone() - E::F::one()));

        // If high_diff < 0, is_greater must be 0
        eval.add_constraint((-high_diff.clone()) * is_greater.clone());

        // todo: need to fix these
        // If high_diff = 0, then low_diff determines is_greater
        // eval.add_constraint(
        //     (E::F::one() - high_diff.clone())
        //         * (low_diff.clone() * (is_greater.clone() - E::F::one())
        //             + (-low_diff.clone()) * is_greater.clone()),
        // );

        eval
    }
}

pub fn generate_trace(
    log_size: u32,
    inputs: &[u64],
    low_bound: u64,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let mut trace = vec![
        vec![M31::zero(); 1 << log_size], // limb0
        vec![M31::zero(); 1 << log_size], // limb1
        vec![M31::zero(); 1 << log_size], // low_limb0
        vec![M31::zero(); 1 << log_size], // low_limb1
        vec![M31::zero(); 1 << log_size], // is_greater
        vec![M31::zero(); 1 << log_size], // high_diff
        vec![M31::zero(); 1 << log_size], // low_diff
    ];

    for (i, &input) in inputs.iter().enumerate() {
        let (input_low, input_high) = store_u64(input);
        let (low_low, low_high) = store_u64(low_bound);

        trace[0][i] = M31::from_u32_unchecked(input_low);
        trace[1][i] = M31::from_u32_unchecked(input_high);
        trace[2][i] = M31::from_u32_unchecked(low_low);
        trace[3][i] = M31::from_u32_unchecked(low_high);

        let high_diff = input_high as i64 - low_high as i64;
        trace[5][i] = M31::from_u32_unchecked(high_diff as u32);

        let low_diff = input_low as i64 - low_low as i64;
        trace[6][i] = M31::from_u32_unchecked(low_diff as u32);

        trace[4][i] = if input > low_bound {
            M31::one()
        } else {
            M31::zero()
        };
    }

    let domain = CanonicCoset::new(log_size).circle_domain();
    trace
        .into_iter()
        .map(|col| {
            CircleEvaluation::<SimdBackend, M31, BitReversedOrder>::new(
                domain,
                BaseColumn::from_iter(col),
            )
        })
        .collect()
}

pub fn prove_limbs(
    log_n_rows: u32,
    input: &[u64],
    low_bound: u64,
    config: PcsConfig,
) -> LimbsProof {
    let mut channel = Blake2sChannel::default();

    let trace = generate_trace(log_n_rows, input, low_bound);

    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_n_rows + config.fri_config.log_blowup_factor + 1)
            .circle_domain()
            .half_coset,
    );
    let mut commitment_scheme =
        CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace.clone());
    tree_builder.commit(&mut channel);

    let component = LimbsComponent::new(
        &mut TraceLocationAllocator::default(),
        LimbsEval { log_n_rows },
    );

    let stark_proof = prove(&[&component], &mut channel, &mut commitment_scheme).unwrap();

    LimbsProof {
        stark_proof,
        component,
    }
}

#[cfg(test)]
mod tests {

    use stwo_prover::core::{air::Component, pcs::CommitmentSchemeVerifier, prover::verify};

    use super::*;
    #[test]
    fn test_limbs_circuit() {
        let input = 9183912831293123u64;
        let low_bound = 9183912831293122u64;

        let input_arr = [input];
        let config = PcsConfig::default();
        let limbs_proof = prove_limbs(3, &input_arr, low_bound, config);

        let proof = limbs_proof.stark_proof;
        let component = limbs_proof.component;
        let sizes = component.trace_log_degree_bounds();

        let verifier_channel = &mut Blake2sChannel::default();
        let commitment_scheme = &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);
        commitment_scheme.commit(proof.commitments[0], &sizes[0], verifier_channel);

        assert!(verify(&[&component], verifier_channel, commitment_scheme, proof).is_ok());
    }
}
