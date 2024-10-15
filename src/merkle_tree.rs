use itertools::Itertools;
use num_traits::Zero;

use stwo_prover::constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, TraceLocationAllocator,
};
use stwo_prover::core::backend::simd::column::BaseColumn;
use stwo_prover::core::backend::simd::SimdBackend;
use stwo_prover::core::backend::Column;
use stwo_prover::core::channel::Blake2sChannel;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::pcs::{CommitmentSchemeProver, PcsConfig};
use stwo_prover::core::poly::circle::{CanonicCoset, CircleEvaluation, PolyOps};
use stwo_prover::core::poly::BitReversedOrder;
use stwo_prover::core::prover::{prove, StarkProof};
use stwo_prover::core::vcs::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo_prover::core::ColumnVec;

#[derive(Clone)]
pub struct MerkleRootEval {
    pub log_n_leaves: u32,
}

pub type MerkleRootComponent = FrameworkComponent<MerkleRootEval>;

impl FrameworkEval for MerkleRootEval {
    fn log_size(&self) -> u32 {
        self.log_n_leaves
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let left = eval.next_trace_mask();
        let right = eval.next_trace_mask();
        let parent = eval.next_trace_mask();

        // (todo) : replace with place poseidon/blake hash
        eval.add_constraint(parent.clone() - (left.clone() + right.clone()));
        eval
    }
}

const N_COLUMNS: usize = 3;

pub fn gen_merkle_trace(
    log_size: u32,
    inputs: &[M31],
) -> ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>> {
    let n_leaves = 1 << log_size;

    let mut trace = (0..N_COLUMNS)
        .map(|_| vec![M31::zero(); n_leaves])
        .collect_vec();

    let domain = CanonicCoset::new(log_size).circle_domain();

    // Level 1: Process leaf nodes
    for i in 0..n_leaves / 2 {
        trace[0][i] = inputs[2 * i];
        trace[1][i] = inputs[2 * i + 1];
        trace[2][i] = trace[0][i] + trace[1][i];
        println!(
            "Level 1 - Node {}: left {:?}, right {:?}, parent {:?}",
            i, trace[0][i].0, trace[1][i].0, trace[2][i].0
        );
    }

    // Process higher levels
    let mut level_size = n_leaves / 2;
    let mut start_index = n_leaves / 2;

    while level_size > 1 {
        for i in 0..level_size / 2 {
            let left = trace[2][start_index - level_size + i * 2];
            let right = trace[2][start_index - level_size + i * 2 + 1];
            let parent = left + right;

            trace[0][start_index + i] = left;
            trace[1][start_index + i] = right;
            trace[2][start_index + i] = parent;

            println!(
                "Level {} - Node {}: left {:?}, right {:?}, parent {:?}",
                (log_size + 1) - (start_index as f32).log2() as u32,
                start_index + i,
                left.0,
                right.0,
                parent.0
            );
        }

        start_index += level_size / 2;
        level_size /= 2;
    }

    trace
        .into_iter()
        .map(|col| {
            CircleEvaluation::<SimdBackend, M31, BitReversedOrder>::new(
                domain,
                BaseColumn::from_iter(col),
            )
        })
        .collect_vec()
}

pub struct MerkleProof {
    pub root: M31,
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
    pub component: FrameworkComponent<MerkleRootEval>,
}

pub fn prove_merkle_tree(log_n_leaves: u32, inputs: &[M31], config: PcsConfig) -> MerkleProof {
    let mut channel = Blake2sChannel::default();

    let trace = gen_merkle_trace(log_n_leaves, inputs);

    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_n_leaves + config.fri_config.log_blowup_factor + 1)
            .circle_domain()
            .half_coset,
    );
    let mut commitment_scheme =
        CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace.clone());
    tree_builder.commit(&mut channel);

    let component = MerkleRootComponent::new(
        &mut TraceLocationAllocator::default(),
        MerkleRootEval { log_n_leaves },
    );

    let stark_proof = prove(&[&component], &mut channel, &mut commitment_scheme).unwrap();

    let root = trace.last().unwrap().at((1 << log_n_leaves) - 2);

    MerkleProof {
        root,
        stark_proof,
        component,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use stwo_prover::core::{
        air::Component,
        fields::m31::BaseField,
        pcs::{CommitmentSchemeVerifier, PcsConfig},
        prover::verify,
    };

    #[test]
    fn test_merkle_tree_circuit() {
        // 2^3 = 8 leaves

        // level 1
        // left 1, right 2, parent 3
        // left 3, right 4, parent 7
        // left 5, right 6, parent 11
        // left 7, right 8, parent 15

        // level 2
        // left 3, right 7, parent 10
        // left 11, right 15, parent 26

        // level 3
        // left 10, right 26, parent 36

        const LOG_N_LEAVES: u32 = 3;
        let config = PcsConfig::default();

        let leaves: Vec<BaseField> = (1..=8).map(|i| M31::from_u32_unchecked(i)).collect();

        let merkle_proof = prove_merkle_tree(LOG_N_LEAVES, &leaves, config);
        let root = merkle_proof.root;
        assert!(root.0 == 36);

        let proof = merkle_proof.stark_proof;
        let component = merkle_proof.component;
        let sizes = component.trace_log_degree_bounds();

        let verifier_channel = &mut Blake2sChannel::default();
        let commitment_scheme = &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);
        commitment_scheme.commit(proof.commitments[0], &sizes[0], verifier_channel);

        assert!(verify(&[&component], verifier_channel, commitment_scheme, proof).is_ok());
    }
}
