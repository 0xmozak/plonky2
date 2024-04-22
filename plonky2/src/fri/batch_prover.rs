#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
use core::cmp::Reverse;
// use core::cmp::Reverse;
use core::iter::once;

use itertools::{chain, izip, Itertools};
use plonky2_field::extension::flatten;
use plonky2_field::types::Field;
use plonky2_maybe_rayon::*;
use plonky2_util::reverse_index_bits_in_place;

use crate::field::extension::{unflatten, Extendable};
use crate::field::polynomial::{PolynomialCoeffs, PolynomialValues};
use crate::fri::proof::{FriInitialTreeProof, FriProof, FriQueryRound, FriQueryStep};
use crate::fri::prover::{fri_proof_of_work, FriCommitedTrees};
use crate::fri::FriParams;
use crate::hash::field_merkle_tree::FieldMerkleTree;
use crate::hash::hash_types::RichField;
use crate::hash::merkle_tree::MerkleTree;
use crate::iop::challenger::Challenger;
use crate::plonk::config::GenericConfig;
use crate::plonk::plonk_common::reduce_with_powers;
use crate::timed;
use crate::util::timing::TimingTree;

/// Builds a batch FRI proof.
pub fn batch_fri_proof<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>(
    initial_merkle_trees: &[&FieldMerkleTree<F, C::Hasher>],
    // TODO(Matthias): this corresponds to the first item in lde_polynomial_values
    // It's silly to treat this special.
    lde_polynomial_values: &[PolynomialValues<F::Extension>],
    challenger: &mut Challenger<F, C::Hasher>,
    fri_params: &FriParams,
    timing: &mut TimingTree,
) -> FriProof<F, C::Hasher, D> {
    // We expect a square shape?
    // No, we expect the first lde_polynomial_values to correspond to lde_polynomial_coeffs?
    // The polynomial vectors should be sorted by degree, from largest to smallest, with no duplicate degrees.
    assert!(lde_polynomial_values
        .windows(2)
        .all(|pair| { pair[0].len() > pair[1].len() }));

    // Commit phase
    let (trees, final_coeffs) = timed!(
        timing,
        "fold codewords in the commitment phase",
        batch_fri_committed_trees::<F, C, D>(lde_polynomial_values, challenger, fri_params,)
    );

    // PoW phase
    let pow_witness = timed!(
        timing,
        "find proof-of-work witness",
        fri_proof_of_work::<F, C, D>(challenger, &fri_params.config)
    );

    let n = lde_polynomial_values[0].len();
    // Query phase
    let query_round_proofs = batch_fri_prover_query_rounds::<F, C, D>(
        initial_merkle_trees,
        &trees,
        challenger,
        n,
        fri_params,
    );

    FriProof {
        commit_phase_merkle_caps: trees.iter().map(|t| t.cap.clone()).collect(),
        query_round_proofs,
        final_poly: final_coeffs,
        pow_witness,
    }
}

pub(crate) fn batch_fri_committed_trees<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    // TODO(Matthias): see about parallelising!
    values: &[PolynomialValues<F::Extension>],
    challenger: &mut Challenger<F, C::Hasher>,
    fri_params: &FriParams,
) -> FriCommitedTrees<F, C, D> {
    let mut acc_coeffs: PolynomialCoeffs<F::Extension> = PolynomialCoeffs::empty();
    // Just for a debug assertion.
    let first_len = values[0].len();

    let arities = fri_params
        .reduction_arity_bits
        .iter()
        .map(|&arity_bits| 1_usize << arity_bits);
    let shifts = arities
        .clone()
        // This is very similar to 'F::powers', but with some jumps.
        .scan(F::coset_shift(), |shift: &mut F, arity| {
            let old_shift = *shift;
            *shift = shift.exp_u64(arity as u64);
            Some(old_shift)
            // shift at time of coset_ifft is actually just a function of first_len / current_len
        });
    let mut values = values.iter().peekable();
    let trees = izip!(arities, shifts)
        .map(|(arity, old_shift)| {
            // TODO(Matthias): improve the condition.
            if Some(acc_coeffs.len()) == values.peek().map(|v| v.len()) || acc_coeffs.len() == 0 {
                // TODO(Matthias): in principle, we can apply all the coset_ifft on value in parallel at the beginning.
                acc_coeffs += &values.next().unwrap().clone().coset_ifft(old_shift.into());
                assert_eq!(old_shift, F::coset_shift().exp_u64((first_len / acc_coeffs.len()) as u64));
            }
            let tree = MerkleTree::<F, C::Hasher>::new(
                {
                    let mut acc_values = acc_coeffs.coset_fft(old_shift.into());
                    reverse_index_bits_in_place(&mut acc_values.values);
                    acc_values.values.par_chunks(arity).map(flatten).collect()
                },
                fri_params.config.cap_height,
            );

            challenger.observe_cap(&tree.cap);

            let beta = challenger.get_extension_challenge::<D>();

            // P(x) = sum_{i<r} x^i * P_i(x^r) becomes sum_{i<r} beta^(i+1) * P_i(x).
            acc_coeffs = PolynomialCoeffs::new(
                acc_coeffs
                    .coeffs
                    .par_chunks_exact(arity)
                    .map(|chunk| reduce_with_powers(chunk, beta) * beta)
                    .collect(),
            );
            tree
        })
        .collect();
    // Make sure we consumed all values:
    assert_eq!(values.next(), None);

    // The coefficients being removed here should always be zero.
    acc_coeffs
        .coeffs
        .truncate(acc_coeffs.len() >> fri_params.config.rate_bits);

    challenger.observe_extension_elements(&acc_coeffs.coeffs);
    // trees.pop();
    // assert_eq!(fri_params.reduction_arity_bits.len(), trees.len());
    (trees, acc_coeffs)
}

fn batch_fri_prover_query_rounds<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    initial_merkle_trees: &[&FieldMerkleTree<F, C::Hasher>],
    trees: &[MerkleTree<F, C::Hasher>],
    challenger: &mut Challenger<F, C::Hasher>,
    n: usize,
    fri_params: &FriParams,
) -> Vec<FriQueryRound<F, C::Hasher, D>> {
    challenger
        .get_n_challenges(fri_params.config.num_query_rounds)
        .into_par_iter()
        .map(|rand| {
            let x_index = rand.to_canonical_u64() as usize % n;
            batch_fri_prover_query_round::<F, C, D>(
                initial_merkle_trees,
                trees,
                x_index,
                fri_params,
            )
        })
        .collect()
}

fn make_initial_trees_proof<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    initial_merkle_trees: &[&FieldMerkleTree<F, C::Hasher>],
    x_index: usize,
) -> FriInitialTreeProof<F, C::Hasher> {
    FriInitialTreeProof {
        evals_proofs: initial_merkle_trees
            .iter()
            .map(|t| {
                (
                    t.values(x_index)
                        .iter()
                        .flatten()
                        .cloned()
                        .collect::<Vec<_>>(),
                    t.open_batch(x_index),
                )
            })
            .collect(),
    }
}

fn make_steps<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>(
    trees: &[MerkleTree<F, C::Hasher>],
    x_index: usize,
    fri_params: &FriParams,
) -> Vec<FriQueryStep<F, C::Hasher, D>> {
    // TODO(Matthias): Right shifting the index goes up in the tree?
    let x_indices = fri_params
        .reduction_arity_bits
        .iter()
        .scan(x_index, |x_index, &arity_bits| {
            *x_index >>= arity_bits;
            Some(*x_index)
        });
    izip!(trees, x_indices)
        .map(|(tree, x_index)| FriQueryStep {
            evals: unflatten(tree.get(x_index)),
            merkle_proof: tree.prove(x_index),
        })
        .collect::<Vec<_>>()
}

fn batch_fri_prover_query_round<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    initial_merkle_trees: &[&FieldMerkleTree<F, C::Hasher>],
    trees: &[MerkleTree<F, C::Hasher>],
    x_index: usize,
    fri_params: &FriParams,
) -> FriQueryRound<F, C::Hasher, D> {
    FriQueryRound {
        initial_trees_proof: make_initial_trees_proof::<F, C, D>(initial_merkle_trees, x_index),
        steps: make_steps::<F, C, D>(trees, x_index, fri_params),
    }
}

#[cfg(test)]
mod tests {
    #[cfg(not(feature = "std"))]
    use alloc::vec;

    use anyhow::Result;
    use plonky2_field::goldilocks_field::GoldilocksField;
    use plonky2_field::types::{Field64, Sample};

    use super::*;
    use crate::fri::batch_oracle::BatchFriOracle;
    use crate::fri::batch_verifier::verify_batch_fri_proof;
    use crate::fri::reduction_strategies::FriReductionStrategy;
    use crate::fri::structure::{
        FriBatchInfo, FriInstanceInfo, FriOpeningBatch, FriOpenings, FriOracleInfo,
        FriPolynomialInfo,
    };
    use crate::fri::FriConfig;
    use crate::plonk::config::PoseidonGoldilocksConfig;

    const D: usize = 2;

    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type H = <C as GenericConfig<D>>::Hasher;

    #[test]
    fn single_polynomial() -> Result<()> {
        let mut timing = TimingTree::default();

        let k = 9;
        let reduction_arity_bits = vec![1, 2, 1];
        let fri_params = FriParams {
            config: FriConfig {
                rate_bits: 1,
                cap_height: 5,
                proof_of_work_bits: 0,
                reduction_strategy: FriReductionStrategy::Fixed(reduction_arity_bits.clone()),
                num_query_rounds: 10,
            },
            hiding: false,
            degree_bits: k,
            reduction_arity_bits,
        };

        let n = 1 << k;
        let trace = PolynomialValues::new((1..n + 1).map(F::from_canonical_i64).collect_vec());

        let polynomial_batch: BatchFriOracle<GoldilocksField, C, D> = BatchFriOracle::from_values(
            vec![trace.clone()],
            fri_params.config.rate_bits,
            fri_params.hiding,
            fri_params.config.cap_height,
            &mut timing,
            &[None],
        );
        let poly = &polynomial_batch.polynomials[0];
        let mut challenger = Challenger::<F, H>::new();
        challenger.observe_cap(&polynomial_batch.field_merkle_tree.cap);
        let _alphas = challenger.get_n_challenges(2);
        let zeta = challenger.get_extension_challenge::<D>();
        challenger.observe_extension_element::<D>(&poly.to_extension::<D>().eval(zeta));
        let mut verifier_challenger = challenger.clone();

        let fri_instance: FriInstanceInfo<F, D> = FriInstanceInfo {
            oracles: vec![FriOracleInfo {
                num_polys: 1,
                blinding: false,
            }],
            batches: vec![FriBatchInfo {
                point: zeta,
                polynomials: vec![FriPolynomialInfo {
                    oracle_index: 0,
                    polynomial_index: 0,
                }],
            }],
        };
        let _alpha = challenger.get_extension_challenge::<D>();

        let composition_poly = poly.mul_extension::<D>(<F as Extendable<D>>::Extension::ONE);
        let mut quotient = composition_poly.divide_by_linear(zeta);
        quotient.coeffs.push(<F as Extendable<D>>::Extension::ZERO);

        let lde_final_poly = quotient.lde(fri_params.config.rate_bits);
        let lde_final_values = lde_final_poly.coset_fft(F::coset_shift().into());

        let proof = batch_fri_proof::<F, C, D>(
            &[&polynomial_batch.field_merkle_tree],
            &[lde_final_values],
            &mut challenger,
            &fri_params,
            &mut timing,
        );

        let fri_challenges = verifier_challenger.fri_challenges::<C, D>(
            &proof.commit_phase_merkle_caps,
            &proof.final_poly,
            proof.pow_witness,
            k,
            &fri_params.config,
        );

        let fri_opening_batch = FriOpeningBatch {
            values: vec![poly.to_extension::<D>().eval(zeta)],
        };
        verify_batch_fri_proof::<GoldilocksField, C, 2>(
            &[k],
            &[&fri_instance],
            &[&FriOpenings {
                batches: vec![fri_opening_batch],
            }],
            &fri_challenges,
            &[polynomial_batch.field_merkle_tree.cap],
            &proof,
            &fri_params,
        )
    }

    #[test]
    fn multiple_polynomials() -> Result<()> {
        let mut timing = TimingTree::default();

        let k0 = 9;
        let k1 = 8;
        let k2 = 6;
        let reduction_arity_bits = vec![1, 2, 1];
        let fri_params = FriParams {
            config: FriConfig {
                rate_bits: 1,
                cap_height: 5,
                proof_of_work_bits: 0,
                reduction_strategy: FriReductionStrategy::Fixed(reduction_arity_bits.clone()),
                num_query_rounds: 10,
            },
            hiding: false,
            degree_bits: k0,
            reduction_arity_bits,
        };

        let n0 = 1 << k0;
        let n1 = 1 << k1;
        let n2 = 1 << k2;
        let trace0 = PolynomialValues::new(F::rand_vec(n0));
        let trace1 = PolynomialValues::new(F::rand_vec(n1));
        let trace2 = PolynomialValues::new(F::rand_vec(n2));

        let trace_oracle: BatchFriOracle<GoldilocksField, C, D> = BatchFriOracle::from_values(
            vec![trace0.clone(), trace1.clone(), trace2.clone()],
            fri_params.config.rate_bits,
            fri_params.hiding,
            fri_params.config.cap_height,
            &mut timing,
            &[None; 3],
        );

        let mut challenger = Challenger::<F, H>::new();
        challenger.observe_cap(&trace_oracle.field_merkle_tree.cap);
        let _alphas = challenger.get_n_challenges(2);
        let zeta = challenger.get_extension_challenge::<D>();
        let poly0 = &trace_oracle.polynomials[0];
        let poly1 = &trace_oracle.polynomials[1];
        let poly2 = &trace_oracle.polynomials[2];
        challenger.observe_extension_element::<D>(&poly0.to_extension::<D>().eval(zeta));
        challenger.observe_extension_element::<D>(&poly1.to_extension::<D>().eval(zeta));
        challenger.observe_extension_element::<D>(&poly2.to_extension::<D>().eval(zeta));
        let mut verifier_challenger = challenger.clone();

        let _alpha = challenger.get_extension_challenge::<D>();

        let composition_poly = poly0.mul_extension::<D>(<F as Extendable<D>>::Extension::ONE);
        let mut quotient = composition_poly.divide_by_linear(zeta);
        quotient.coeffs.push(<F as Extendable<D>>::Extension::ZERO);
        let lde_final_poly_0 = quotient.lde(fri_params.config.rate_bits);
        let lde_final_values_0 = lde_final_poly_0.coset_fft(F::coset_shift().into());

        let composition_poly = poly1.mul_extension::<D>(<F as Extendable<D>>::Extension::ONE);
        let mut quotient = composition_poly.divide_by_linear(zeta);
        quotient.coeffs.push(<F as Extendable<D>>::Extension::ZERO);
        let lde_final_poly_1 = quotient.lde(fri_params.config.rate_bits);
        let lde_final_values_1 = lde_final_poly_1.coset_fft(F::coset_shift().into());

        let composition_poly = poly2.mul_extension::<D>(<F as Extendable<D>>::Extension::ONE);
        let mut quotient = composition_poly.divide_by_linear(zeta);
        quotient.coeffs.push(<F as Extendable<D>>::Extension::ZERO);
        let lde_final_poly_2 = quotient.lde(fri_params.config.rate_bits);
        let lde_final_values_2 = lde_final_poly_2.coset_fft(F::coset_shift().into());

        let proof = batch_fri_proof::<F, C, D>(
            &[&trace_oracle.field_merkle_tree],
            &[lde_final_values_0, lde_final_values_1, lde_final_values_2],
            &mut challenger,
            &fri_params,
            &mut timing,
        );

        let fri_instance = &FriInstanceInfo {
            oracles: vec![FriOracleInfo {
                num_polys: 1,
                blinding: false,
            }],
            batches: vec![FriBatchInfo {
                point: zeta,
                polynomials: vec![FriPolynomialInfo {
                    oracle_index: 0,
                    polynomial_index: 0,
                }],
            }],
        };
        let fri_instances = vec![fri_instance, fri_instance, fri_instance];
        let fri_challenges = verifier_challenger.fri_challenges::<C, D>(
            &proof.commit_phase_merkle_caps,
            &proof.final_poly,
            proof.pow_witness,
            k0,
            &fri_params.config,
        );
        let fri_opening_batch_0 = &FriOpenings {
            batches: vec![FriOpeningBatch {
                values: vec![poly0.to_extension::<D>().eval(zeta)],
            }],
        };
        let fri_opening_batch_1 = &FriOpenings {
            batches: vec![FriOpeningBatch {
                values: vec![poly1.to_extension::<D>().eval(zeta)],
            }],
        };
        let fri_opening_batch_2 = &FriOpenings {
            batches: vec![FriOpeningBatch {
                values: vec![poly2.to_extension::<D>().eval(zeta)],
            }],
        };
        let fri_openings = vec![
            fri_opening_batch_0,
            fri_opening_batch_1,
            fri_opening_batch_2,
        ];

        verify_batch_fri_proof::<GoldilocksField, C, 2>(
            &[k0, k1, k2],
            &fri_instances,
            &fri_openings,
            &fri_challenges,
            &[trace_oracle.field_merkle_tree.cap],
            &proof,
            &fri_params,
        )
    }
}
