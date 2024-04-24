#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

use itertools::Itertools;
use plonky2_field::extension::Extendable;
use plonky2_field::fft::FftRootTable;
use plonky2_field::polynomial::{PolynomialCoeffs, PolynomialValues};
use plonky2_maybe_rayon::*;
use plonky2_util::{log2_strict, reverse_index_bits_in_place};

use crate::fri::oracle::PolynomialBatch;
use crate::hash::field_merkle_tree::FieldMerkleTree;
use crate::hash::hash_types::RichField;
use crate::plonk::config::GenericConfig;
use crate::timed;
use crate::util::timing::TimingTree;
use crate::util::transpose;

/// Represents a batch FRI oracle, i.e. a batch of polynomials with different degrees which have
/// been Merkle-ized in a Field Merkle Tree.
#[derive(Eq, PartialEq, Debug)]
pub struct BatchFriOracle<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>
{
    pub polynomials: Vec<PolynomialCoeffs<F>>,
    pub field_merkle_tree: FieldMerkleTree<F, C::Hasher>,
    pub degree_logs: Vec<usize>,
    pub rate_bits: usize,
    pub blinding: bool,
}

impl<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>
    BatchFriOracle<F, C, D>
{
    /// Creates a list polynomial commitment for the polynomials interpolating the values in `values`.
    pub fn from_values(
        values: Vec<PolynomialValues<F>>,
        rate_bits: usize,
        blinding: bool,
        cap_height: usize,
        timing: &mut TimingTree,
        fft_root_table: &[Option<&FftRootTable<F>>],
    ) -> Self {
        let coeffs = timed!(
            timing,
            "IFFT",
            values.into_par_iter().map(|v| v.ifft()).collect::<Vec<_>>()
        );

        Self::from_coeffs(
            coeffs,
            rate_bits,
            blinding,
            cap_height,
            timing,
            fft_root_table,
        )
    }

    /// Creates a list polynomial commitment for the polynomials `polynomials`.
    pub fn from_coeffs(
        polynomials: Vec<PolynomialCoeffs<F>>,
        rate_bits: usize,
        blinding: bool,
        cap_height: usize,
        timing: &mut TimingTree,
        fft_root_table: &[Option<&FftRootTable<F>>],
    ) -> Self {
        let degree_logs = polynomials
            .iter()
            .map(|p| log2_strict(p.len()))
            .collect_vec();
        assert!(degree_logs.windows(2).all(|pair| { pair[0] >= pair[1] }));
        let max_degree_log = degree_logs[0];

        let num_polynomials = polynomials.len();
        let mut group_start = 0;
        let mut leaves = Vec::new();
        let shift = F::coset_shift();

        for (i, d) in degree_logs.iter().enumerate() {
            if i == num_polynomials - 1 || *d > degree_logs[i + 1] {
                let lde_values = timed!(
                    timing,
                    "FFT + blinding",
                    PolynomialBatch::<F, C, D>::lde_values(
                        &polynomials[group_start..i + 1],
                        rate_bits,
                        shift.exp_power_of_2(max_degree_log - d),
                        blinding,
                        fft_root_table[i]
                    )
                );

                let mut leaf_group = timed!(timing, "transpose LDEs", transpose(&lde_values));
                reverse_index_bits_in_place(&mut leaf_group);
                leaves.push(leaf_group);

                group_start = i + 1;
            }
        }

        let field_merkle_tree = timed!(
            timing,
            "build Field Merkle tree",
            FieldMerkleTree::new(leaves, cap_height)
        );

        Self {
            polynomials,
            field_merkle_tree,
            degree_logs,
            rate_bits,
            blinding,
        }
    }

    /// Produces a batch opening proof.
    pub fn prove_openings(
        instances: &[FriInstanceInfo<F, D>],
        oracles: &[&Self],
        challenger: &mut Challenger<F, C::Hasher>,
        fri_params: &FriParams,
        timing: &mut TimingTree,
    ) -> FriProof<F, C::Hasher, D> {
        assert!(D > 1, "Not implemented for D=1.");
        let alpha = challenger.get_extension_challenge::<D>();
        let mut alpha = ReducingFactor::new(alpha);

        let mut final_lde_polynomial_coeff = PolynomialCoeffs::empty();
        let mut final_lde_polynomial_values = Vec::with_capacity(instances.len());
        for (i, instance) in instances.iter().enumerate() {
            // Final low-degree polynomial that goes into FRI.
            let mut final_poly = PolynomialCoeffs::empty();

            // Each batch `i` consists of an opening point `z_i` and polynomials `{f_ij}_j` to be opened at that point.
            // For each batch, we compute the composition polynomial `F_i = sum alpha^j f_ij`,
            // where `alpha` is a random challenge in the extension field.
            // The final polynomial is then computed as `final_poly = sum_i alpha^(k_i) (F_i(X) - F_i(z_i))/(X-z_i)`
            // where the `k_i`s are chosen such that each power of `alpha` appears only once in the final sum.
            // There are usually two batches for the openings at `zeta` and `g * zeta`.
            // The oracles used in Plonky2 are given in `FRI_ORACLES` in `plonky2/src/plonk/plonk_common.rs`.
            for FriBatchInfo { point, polynomials } in &instance.batches {
                // Collect the coefficients of all the polynomials in `polynomials`.
                let polys_coeff = polynomials.iter().map(|fri_poly| {
                    &oracles[fri_poly.oracle_index].polynomials[fri_poly.polynomial_index]
                });
                let composition_poly = timed!(
                    timing,
                    &format!("reduce batch of {} polynomials", polynomials.len()),
                    alpha.reduce_polys_base(polys_coeff)
                );
                let mut quotient = composition_poly.divide_by_linear(*point);
                quotient.coeffs.push(F::Extension::ZERO); // pad back to power of two
                alpha.shift_poly(&mut final_poly);
                final_poly += quotient;
            }

            let lde_final_poly = final_poly.lde(fri_params.config.rate_bits);
            let lde_final_values = timed!(
                timing,
                &format!("perform final FFT {}", lde_final_poly.len()),
                lde_final_poly.coset_fft(F::coset_shift().into())
            );
            final_lde_polynomial_values.push(lde_final_values);
            if i == 0 {
                final_lde_polynomial_coeff = lde_final_poly;
            }
        }

        batch_fri_proof::<F, C, D>(
            &oracles.iter().map(|o|&o.field_merkle_tree).collect::<Vec<_>>(),
            final_lde_polynomial_coeff,
            &final_lde_polynomial_values,
            challenger,
            fri_params,
            timing,
        )
    }
}
