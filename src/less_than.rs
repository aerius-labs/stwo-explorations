use itertools::Itertools;
use num_traits::One;
use num_traits::Zero;

use stwo_prover::constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, TraceLocationAllocator,
};
use stwo_prover::core::backend::simd::m31::PackedBaseField;
use stwo_prover::core::backend::simd::SimdBackend;
use stwo_prover::core::backend::{Col, Column};
use stwo_prover::core::channel::Blake2sChannel;
use stwo_prover::core::fields::m31::BaseField;
use stwo_prover::core::pcs::{CommitmentSchemeProver, PcsConfig};
use stwo_prover::core::poly::circle::{CanonicCoset, CircleEvaluation, PolyOps};
use stwo_prover::core::poly::BitReversedOrder;
use stwo_prover::core::prover::{prove, StarkProof};
use stwo_prover::core::vcs::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo_prover::core::ColumnVec;

#[derive(Clone)]
pub struct LessThanEval {
    pub log_n_rows: u32,
}

pub type LessThanComponent = FrameworkComponent<LessThanEval>;

impl FrameworkEval for LessThanEval {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let a = eval.next_trace_mask();
        let b = eval.next_trace_mask();
        let diff = eval.next_trace_mask();
        let is_less_than = eval.next_trace_mask();

        // Constraint: diff = b - a
        eval.add_constraint(diff.clone() - (b.clone() - a.clone()));

        // Constraint: is_less_than * (1 - is_less_than) = 0 (boolean constraint)
        eval.add_constraint(is_less_than.clone() * (E::F::one() - is_less_than.clone()));

        // Constraint: is_less_than * diff = diff (if a < b, then diff > 0 and is_less_than = 1)
        eval.add_constraint(is_less_than.clone() * diff.clone() - diff);

        // Constraint: (1 - is_less_than) * (b - a) = 0 (if a >= b, then is_less_than = 0)
        eval.add_constraint((E::F::one() - is_less_than) * (b - a));

        eval
    }
}

pub fn generate_less_than_trace(
    log_size: u32,
    inputs_a: &[PackedBaseField],
    inputs_b: &[PackedBaseField],
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let mut trace = (0..4)
        .map(|_| Col::<SimdBackend, BaseField>::zeros(1 << log_size))
        .collect_vec();

    for (vec_index, (&input_a, &input_b)) in inputs_a.iter().zip(inputs_b.iter()).enumerate() {
        trace[0].data[vec_index] = input_a; // a
        trace[1].data[vec_index] = input_b; // b
        trace[2].data[vec_index] = input_b - input_a; // diff
        trace[3].data[vec_index] = PackedBaseField::from(
            if input_a
                .to_array()
                .iter()
                .zip(input_b.to_array().iter())
                .all(|(&a, &b)| a < b)
            {
                BaseField::one()
            } else {
                BaseField::zero()
            },
        );
    }

    let domain = CanonicCoset::new(log_size).circle_domain();

    trace
        .into_iter()
        .map(|eval| CircleEvaluation::<SimdBackend, _, BitReversedOrder>::new(domain, eval))
        .collect_vec()
}

pub fn prove_less_than(
    log_n_instances: u32,
    inputs_a: &[PackedBaseField],
    inputs_b: &[PackedBaseField],
    config: PcsConfig,
) -> (LessThanComponent, StarkProof<Blake2sMerkleHasher>) {
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_n_instances + config.fri_config.log_blowup_factor + 1)
            .circle_domain()
            .half_coset,
    );

    let prover_channel = &mut Blake2sChannel::default();
    let commitment_scheme =
        &mut CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

    let trace = generate_less_than_trace(log_n_instances, inputs_a, inputs_b);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace);
    tree_builder.commit(prover_channel);

    let component = LessThanComponent::new(
        &mut TraceLocationAllocator::default(),
        LessThanEval {
            log_n_rows: log_n_instances,
        },
    );

    let proof = prove::<SimdBackend, Blake2sMerkleChannel>(
        &[&component],
        prover_channel,
        commitment_scheme,
    )
    .unwrap();

    (component, proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    use stwo_prover::core::air::Component;
    use stwo_prover::core::pcs::{CommitmentSchemeVerifier, TreeVec};
    use stwo_prover::core::prover::verify;

    fn generate_test_inputs(a: u32, b: u32) -> (Vec<PackedBaseField>, Vec<PackedBaseField>) {
        let input_a = vec![PackedBaseField::from(BaseField::from_u32_unchecked(a))];
        let input_b = vec![PackedBaseField::from(BaseField::from_u32_unchecked(b))];
        (input_a, input_b)
    }

    #[test]
    fn test_less_than_prove_and_verify() {
        const LOG_N_ROWS: u32 = 4;
        // a , b , diff , is_less_than
        let config = PcsConfig::default();
        let (inputs_a, inputs_b) = generate_test_inputs(5, 7);

        let (component, proof) = prove_less_than(LOG_N_ROWS, &inputs_a, &inputs_b, config);

        let trace = generate_less_than_trace(LOG_N_ROWS, &inputs_a, &inputs_b);

        println!("a: {:?}", trace[0].values.data[0].to_array()[0]);
        println!("b: {:?}", trace[1].values.data[0].to_array()[0]);
        println!("diff: {:?}", trace[2].values.data[0].to_array()[0]);
        println!("is_less_than: {:?}", trace[3].values.data[0].to_array()[0]);

        let verifier_channel = &mut Blake2sChannel::default();
        let commitment_scheme = &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);

        let sizes = component.trace_log_degree_bounds();
        commitment_scheme.commit(proof.commitments[0], &sizes[0], verifier_channel);

        assert!(verify(&[&component], verifier_channel, commitment_scheme, proof).is_ok());
    }
}
