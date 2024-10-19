use num_traits::One;
use num_traits::Zero;
use stwo_prover::constraint_framework::TraceLocationAllocator;
use stwo_prover::core::backend::simd::column::BaseColumn;
use stwo_prover::core::backend::Column;
use stwo_prover::core::channel::Blake2sChannel;
use stwo_prover::core::pcs::CommitmentSchemeProver;
use stwo_prover::core::pcs::PcsConfig;
use stwo_prover::core::poly::circle::PolyOps;
use stwo_prover::core::prover::prove;
use stwo_prover::core::prover::StarkProof;
use stwo_prover::core::vcs::blake2_merkle::Blake2sMerkleChannel;
use stwo_prover::core::vcs::blake2_merkle::Blake2sMerkleHasher;
use stwo_prover::{
    constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval},
    core::{
        backend::simd::SimdBackend,
        fields::m31::M31,
        poly::{
            circle::{CanonicCoset, CircleEvaluation},
            BitReversedOrder,
        },
        ColumnVec,
    },
};

#[derive(Clone)]
pub struct MerkleRootEval {
    pub log_n_leaves: u32,
}

pub type MerkleRootComponent = FrameworkComponent<MerkleRootEval>;

pub struct MerkleProof {
    pub root: M31,
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
    pub component: FrameworkComponent<MerkleRootEval>,
}

impl FrameworkEval for MerkleRootEval {
    fn log_size(&self) -> u32 {
        self.log_n_leaves
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let current = eval.next_trace_mask();
        let sibling = eval.next_trace_mask();
        let is_left = eval.next_trace_mask();
        let parent = eval.next_trace_mask();

        // is_leaf col is boolean column
        eval.add_constraint(is_left.clone() * (is_left.clone() - E::F::one()));

        // (todo) : replace with place poseidon/blake hash
        eval.add_constraint(parent.clone() - (current.clone() + sibling.clone()));

        // based on is_left, parent should be either current + sibling or sibling + current
        let constraint = parent.clone()
            - (current.clone() + sibling.clone()) * is_left.clone()
            - (sibling.clone() + current.clone()) * (E::F::one() - is_left.clone());

        eval.add_constraint(constraint);
        eval
    }
}

pub fn gen_merkle_trace(
    log_size: u32,
    leaf: &M31,
    proof: &[M31],
    proof_helper: &[M31],
) -> ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>> {
    let n_leaves = 1 << log_size;

    // Initialize trace columns
    let mut current = vec![M31::zero(); n_leaves];
    let mut sibling = vec![M31::zero(); n_leaves];
    let mut is_left = vec![M31::zero(); n_leaves];
    let mut parent = vec![M31::zero(); n_leaves];

    current[0] = *leaf;

    for i in 0..proof.len() {
        sibling[i] = proof[i];
        is_left[i] = proof_helper[i];

        if proof_helper[i] == M31::one() {
            parent[i] = current[i] + sibling[i]; // Todo(vikas): replace with hash function
        } else {
            // Current node is right child
            parent[i] = sibling[i] + current[i]; // Todo(vikas): replace with hash function
        }

        // Set up for next level
        if i < proof.len() - 1 {
            current[i + 1] = parent[i];
        }
    }

    let trace = vec![
        current.clone(),
        sibling.clone(),
        is_left.clone(),
        parent.clone(),
    ];

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

pub fn prove_merkle_tree(
    log_n_leaves: u32,
    leaf: &M31,
    proof: &[M31],
    proof_helper: &[M31],
    config: PcsConfig,
) -> MerkleProof {
    let mut channel = Blake2sChannel::default();

    let trace = gen_merkle_trace(log_n_leaves, leaf, proof, proof_helper);

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

    let root_col = proof.len() - 1;
    let root = trace.last().unwrap().at(root_col);

    MerkleProof {
        root,
        stark_proof,
        component,
    }
}

#[cfg(test)]
mod tests {

    use stwo_prover::core::{air::Component, pcs::CommitmentSchemeVerifier, prover::verify};

    use super::*;

    #[test]
    fn test_merkle_tree_circuit() {
        // Example Test Case Merkle Tree
        //
        //               ROOT (130)
        //             /          \
        //        (59)            (71)
        //        /    \         /    \
        //    (27)    (32)     (35)   (36)
        //    /  \    /  \     /  \    /  \
        //  (12)(15)(16)(16) (17)(18)(19)(17)

        // Merkle proof for leaf 16:
        // Proof values: [16, 27, 71]
        // Proof helper: [0, 1, 0]  (0 for right sibling, 1 for left sibling)

        let leaf = M31::from_u32_unchecked(16);
        let proof = vec![
            M31::from_u32_unchecked(16), // Sibling at level 0
            M31::from_u32_unchecked(27), // Sibling at level 1
            M31::from_u32_unchecked(71), // Sibling at level 2
        ];
        let proof_helper = vec![
            M31::zero(), // Right sibling at level 0
            M31::one(),  // Left sibling at level 1
            M31::zero(), // Right sibling at level 2
        ];

        let config = PcsConfig::default();
        let merkle_proof = prove_merkle_tree(2, &leaf, &proof, &proof_helper, config);
        let proof = merkle_proof.stark_proof;

        let root = merkle_proof.root;
        assert!(root.0 == 130);

        let component = merkle_proof.component;
        let sizes = component.trace_log_degree_bounds();

        let verifier_channel = &mut Blake2sChannel::default();
        let commitment_scheme = &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);
        commitment_scheme.commit(proof.commitments[0], &sizes[0], verifier_channel);

        assert!(verify(&[&component], verifier_channel, commitment_scheme, proof).is_ok());
    }
}
