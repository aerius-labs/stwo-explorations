use itertools::Itertools;

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

pub type SquareComponent = FrameworkComponent<SquareEval>;

#[derive(Clone)]
pub struct SquareEval {
    pub log_n_rows: u32,
}

impl FrameworkEval for SquareEval {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let n = eval.next_trace_mask();
        let square = eval.next_trace_mask();

        eval.add_constraint(square.clone() - n.clone() * n.clone());

        // y^2 - n * n === 0
        eval
    }
}

pub fn generate_square_trace(
    log_size: u32,
    inputs: &[PackedBaseField],
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let mut trace = (0..2)
        .map(|_| Col::<SimdBackend, BaseField>::zeros(1 << log_size))
        .collect_vec();

    for (vec_index, &input) in inputs.iter().enumerate() {
        trace[0].data[vec_index] = input; // n
        trace[1].data[vec_index] = input * input; // n^2
    }

    let domain = CanonicCoset::new(log_size).circle_domain();

    trace
        .into_iter()
        .map(|eval| CircleEvaluation::<SimdBackend, _, BitReversedOrder>::new(domain, eval))
        .collect_vec()
}

pub fn prove_square(
    log_n_instances: u32,
    inputs: &[PackedBaseField],
    config: PcsConfig,
) -> (SquareComponent, StarkProof<Blake2sMerkleHasher>) {
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_n_instances + 1 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    );

    let prover_channel = &mut Blake2sChannel::default();
    let commitment_scheme =
        &mut CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

    let trace = generate_square_trace(log_n_instances, inputs);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace);
    tree_builder.commit(prover_channel);

    let component = SquareComponent::new(
        &mut TraceLocationAllocator::default(),
        SquareEval {
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
    use num_traits::{One, Zero};

    use super::*;
    use stwo_prover::core::air::Component;
    use stwo_prover::core::backend::simd::m31::LOG_N_LANES;
    use stwo_prover::core::pcs::{CommitmentSchemeVerifier, TreeVec};
    use stwo_prover::core::prover::verify;

    fn generate_test_inputs(log_n_instances: u32) -> Vec<PackedBaseField> {
        if log_n_instances < LOG_N_LANES {
            let n_instances = 1 << log_n_instances;
            vec![PackedBaseField::from_array(std::array::from_fn(|j| {
                if j < n_instances {
                    BaseField::from_u32_unchecked(j as u32)
                } else {
                    BaseField::zero()
                }
            }))]
        } else {
            (0..(1 << (log_n_instances - LOG_N_LANES)))
                .map(|i| {
                    PackedBaseField::from_array(std::array::from_fn(|j| {
                        BaseField::from_u32_unchecked((i * 16 + j) as u32)
                    }))
                })
                .collect_vec()
        }
    }

    #[test]
    fn test_square_constraints() {
        const LOG_N_INSTANCES: u32 = 6;
        // 2^6 = 64 instances
        let inputs = generate_test_inputs(LOG_N_INSTANCES);

        let trace = generate_square_trace(LOG_N_INSTANCES, &inputs);

        let traces = TreeVec::new(vec![trace]);
        let trace_polys =
            traces.map(|trace| trace.into_iter().map(|c| c.interpolate()).collect_vec());

        stwo_prover::constraint_framework::assert_constraints(
            &trace_polys,
            CanonicCoset::new(LOG_N_INSTANCES),
            |eval| {
                SquareEval {
                    log_n_rows: LOG_N_INSTANCES,
                }
                .evaluate(eval);
            },
        );
    }

    #[test]
    fn test_square_prove_and_verify() {
        for log_n_instances in 2..=6 {
            let config = PcsConfig::default();
            let inputs = generate_test_inputs(log_n_instances);

            let (component, proof) = prove_square(log_n_instances, &inputs, config);

            // Verify
            let verifier_channel = &mut Blake2sChannel::default();
            let commitment_scheme =
                &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);

            let sizes = component.trace_log_degree_bounds();
            commitment_scheme.commit(proof.commitments[0], &sizes[0], verifier_channel);

            assert!(verify(&[&component], verifier_channel, commitment_scheme, proof).is_ok());
        }
    }

    #[test]
    #[should_panic]
    fn test_square_fails_with_incorrect_output() {
        const LOG_N_INSTANCES: u32 = 6;
        let inputs = generate_test_inputs(LOG_N_INSTANCES);
        let mut trace = generate_square_trace(LOG_N_INSTANCES, &inputs);

        trace[1].values.set(0, BaseField::one());

        let traces = TreeVec::new(vec![trace]);
        let trace_polys =
            traces.map(|trace| trace.into_iter().map(|c| c.interpolate()).collect_vec());

        stwo_prover::constraint_framework::assert_constraints(
            &trace_polys,
            CanonicCoset::new(LOG_N_INSTANCES),
            |eval| {
                SquareEval {
                    log_n_rows: LOG_N_INSTANCES,
                }
                .evaluate(eval);
            },
        );
    }
}
