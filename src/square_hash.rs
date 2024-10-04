use crate::square::{generate_square_trace, SquareEval};
use itertools::Itertools;
use stwo_prover::constraint_framework::constant_columns::gen_is_first;
use stwo_prover::constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, TraceLocationAllocator,
};
use stwo_prover::core::backend::simd::m31::{PackedBaseField, LOG_N_LANES};
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
use stwo_prover::examples::poseidon::{
    gen_trace as poseidon_gen_trace, PoseidonElements, PoseidonEval,
};

pub type SquarePoseidonComponent = FrameworkComponent<SquarePoseidonEval>;

#[derive(Clone)]
pub struct SquarePoseidonEval {
    pub square: SquareEval,
    pub poseidon: PoseidonEval,
}

impl FrameworkEval for SquarePoseidonEval {
    fn log_size(&self) -> u32 {
        std::cmp::max(self.square.log_size(), self.poseidon.log_size())
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        std::cmp::max(
            self.square.max_constraint_log_degree_bound(),
            self.poseidon.max_constraint_log_degree_bound(),
        )
    }

    fn evaluate<E: EvalAtRow>(&self, eval: E) -> E {
        let eval_after_square = self.square.evaluate(eval);
        self.poseidon.evaluate(eval_after_square)
    }
}

pub fn generate_trace(
    log_size: u32,
    inputs: &[PackedBaseField],
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let mut trace = Vec::new();

    let square_log_size = log_size.min(inputs.len().trailing_zeros());
    let mut square_trace = (0..2)
        .map(|_| Col::<SimdBackend, BaseField>::zeros(1 << square_log_size))
        .collect_vec();

    for (vec_index, &input) in inputs.iter().enumerate().take(1 << square_log_size) {
        square_trace[0].data[vec_index] = input; // n
        square_trace[1].data[vec_index] = input * input; // n^2
    }

    trace.extend(square_trace.into_iter().map(|col| {
        let mut extended_col = Col::<SimdBackend, BaseField>::zeros(1 << log_size);
        extended_col.data[..1 << square_log_size].copy_from_slice(&col.data);
        extended_col
    }));

    let (poseidon_trace, _) = poseidon_gen_trace(log_size);
    trace.extend(poseidon_trace.into_iter().map(|eval| eval.values));

    let domain = CanonicCoset::new(log_size).circle_domain();

    trace
        .into_iter()
        .map(|eval| CircleEvaluation::<SimdBackend, _, BitReversedOrder>::new(domain, eval))
        .collect()
}

pub fn prove_square_poseidon(
    log_n_instances: u32,
    inputs: &[PackedBaseField],
    config: PcsConfig,
) -> (SquarePoseidonComponent, StarkProof<Blake2sMerkleHasher>) {
    let log_n_rows = std::cmp::max(log_n_instances, LOG_N_LANES);

    println!(
        "log_n_instances: {}, log_n_rows: {}",
        log_n_instances, log_n_rows
    );

    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_n_rows + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    );

    let channel = &mut Blake2sChannel::default();
    let commitment_scheme =
        &mut CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);

    let square_trace = generate_square_trace(log_n_instances, inputs);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(square_trace);
    tree_builder.commit(channel);

    let (poseidon_trace, lookup_data) = stwo_prover::examples::poseidon::gen_trace(log_n_rows);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(poseidon_trace);
    tree_builder.commit(channel);

    let lookup_elements = PoseidonElements::draw(channel);

    let (interaction_trace, total_sum) = stwo_prover::examples::poseidon::gen_interaction_trace(
        log_n_rows,
        lookup_data,
        &lookup_elements,
    );

    println!("Interaction trace size: {}", interaction_trace.len());
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction_trace);
    tree_builder.commit(channel);

    let mut tree_builder = commitment_scheme.tree_builder();

    let constant_trace = vec![gen_is_first(log_n_rows)];
    println!("Constant trace size: {}", constant_trace.len());
    tree_builder.extend_evals(constant_trace);
    tree_builder.commit(channel);

    let component = SquarePoseidonComponent::new(
        &mut TraceLocationAllocator::default(),
        SquarePoseidonEval {
            square: SquareEval {
                log_n_rows: log_n_instances,
            },
            poseidon: PoseidonEval {
                log_n_rows,
                lookup_elements,
                total_sum,
            },
        },
    );

    let proof = prove(&[&component], channel, commitment_scheme).unwrap();

    (component, proof)
}
