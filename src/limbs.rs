use num_traits::{One, Zero};
use prettytable::{row, Table};
use stwo_prover::constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, TraceLocationAllocator,
};
use stwo_prover::core::backend::simd::column::BaseColumn;
use stwo_prover::core::backend::simd::SimdBackend;
use stwo_prover::core::channel::Blake2sChannel;
use stwo_prover::core::fields::m31::{BaseField, M31};
use stwo_prover::core::pcs::{CommitmentSchemeProver, PcsConfig};
use stwo_prover::core::poly::circle::{CanonicCoset, CircleEvaluation, PolyOps};
use stwo_prover::core::poly::BitReversedOrder;
use stwo_prover::core::prover::{prove, StarkProof};
use stwo_prover::core::vcs::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo_prover::core::ColumnVec;

pub fn store_u16(value: u64) -> (u16, u16, u16, u16) {
    let lower = value as u16;
    let upper = (value >> 16) as u16;
    let upper_upper = (value >> 32) as u16;
    let upper_upper_upper = (value >> 48) as u16;
    (lower, upper, upper_upper, upper_upper_upper)
}

pub fn reconstruct_u64_from_u16(
    lower: u16,
    upper: u16,
    upper_upper: u16,
    upper_upper_upper: u16,
) -> u64 {
    ((upper_upper_upper as u64) << 48)
        | ((upper_upper as u64) << 32)
        | ((upper as u64) << 16)
        | (lower as u64)
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
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let limb0 = eval.next_trace_mask();
        let limb1 = eval.next_trace_mask();
        let limb2 = eval.next_trace_mask();
        let limb3 = eval.next_trace_mask();

        let low_limb0 = eval.next_trace_mask();
        let low_limb1 = eval.next_trace_mask();
        let low_limb2 = eval.next_trace_mask();
        let low_limb3 = eval.next_trace_mask();

        let result = eval.next_trace_mask();
        let gt0 = eval.next_trace_mask();
        let gt1 = eval.next_trace_mask();
        let gt2 = eval.next_trace_mask();
        let gt3 = eval.next_trace_mask();

        eval.add_constraint(result.clone() * (result.clone() - E::F::one()));

        eval.add_constraint(gt0.clone() * (gt0.clone() - E::F::one()));
        eval.add_constraint(gt1.clone() * (gt1.clone() - E::F::one()));
        eval.add_constraint(gt2.clone() * (gt2.clone() - E::F::one()));
        eval.add_constraint(gt3.clone() * (gt3.clone() - E::F::one()));

        let should_be_result = gt3.clone()
            + (E::F::one() - gt3.clone()) * gt2.clone()
            + (E::F::one() - gt3.clone()) * (E::F::one() - gt2.clone()) * gt1.clone()
            + (E::F::one() - gt3.clone())
                * (E::F::one() - gt2.clone())
                * (E::F::one() - gt1.clone())
                * gt0.clone();

        eval.add_constraint(result - should_be_result);

        eval
    }
}

pub fn generate_trace(
    log_size: u32,
    inputs: &[u64],
    low_bound: u64,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let mut trace = vec![
        vec![M31::zero(); 1 << log_size],
        vec![M31::zero(); 1 << log_size],
        vec![M31::zero(); 1 << log_size],
        vec![M31::zero(); 1 << log_size],
        vec![M31::zero(); 1 << log_size],
        vec![M31::zero(); 1 << log_size],
        vec![M31::zero(); 1 << log_size],
        vec![M31::zero(); 1 << log_size],
        vec![M31::zero(); 1 << log_size],
        vec![M31::zero(); 1 << log_size],
        vec![M31::zero(); 1 << log_size],
        vec![M31::zero(); 1 << log_size],
        vec![M31::zero(); 1 << log_size],
    ];

    for (i, &input) in inputs.iter().enumerate() {
        let (limb0, limb1, limb2, limb3) = store_u16(input);
        let (low_limb0, low_limb1, low_limb2, low_limb3) = store_u16(low_bound);

        trace[0][i] = M31::from_u32_unchecked(limb0 as u32); // limb0
        trace[1][i] = M31::from_u32_unchecked(limb1 as u32); // limb1
        trace[2][i] = M31::from_u32_unchecked(limb2 as u32); // limb2
        trace[3][i] = M31::from_u32_unchecked(limb3 as u32); // limb3

        trace[4][i] = M31::from_u32_unchecked(low_limb0 as u32); // low_limb0
        trace[5][i] = M31::from_u32_unchecked(low_limb1 as u32); // low_limb1
        trace[6][i] = M31::from_u32_unchecked(low_limb2 as u32); // low_limb2
        trace[7][i] = M31::from_u32_unchecked(low_limb3 as u32); // low_limb3

        trace[8][i] = if input > low_bound {
            M31::one()
        } else {
            M31::zero()
        };

        trace[9][i] = if (limb0 as i32 - low_limb0 as i32) > 0 {
            M31::one()
        } else {
            M31::zero()
        };

        trace[10][i] = if (limb1 as i32 - low_limb1 as i32) > 0 {
            M31::one()
        } else {
            M31::zero()
        };

        trace[11][i] = if (limb2 as i32 - low_limb2 as i32) > 0 {
            M31::one()
        } else {
            M31::zero()
        };

        trace[12][i] = if (limb3 as i32 - low_limb3 as i32) > 0 {
            M31::one()
        } else {
            M31::zero()
        };
    }
    // just for debugging. need to remove later!
    let mut table = Table::new();
    table.add_row(row![
        "limb0",
        "limb1",
        "limb2",
        "limb3",
        "low_limb0",
        "low_limb1",
        "low_limb2",
        "low_limb3",
        "result",
        "gt0",
        "gt1",
        "gt2",
        "gt3"
    ]);

    for i in 0..2 {
        table.add_row(row![
            trace[0][i],
            trace[1][i],
            trace[2][i],
            trace[3][i],
            trace[4][i],
            trace[5][i],
            trace[6][i],
            trace[7][i],
            trace[8][i],
            trace[9][i],
            trace[10][i],
            trace[11][i],
            trace[12][i]
        ]);
    }

    table.printstd();

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
        let input1 = 0x1234_5678_9ABC_DEF2u64; // u64
        let input2 = 0x1234_5678_9ABC_DEF0;
        let low_bound = 0x1234_5678_9ABC_DEF1u64;

        let input_arr = [input2, input1];
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
