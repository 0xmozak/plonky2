#[cfg(not(feature = "std"))]
use alloc::{vec, vec::Vec};
use core::mem::size_of;

use itertools::Itertools;
use tiny_keccak::{Hasher as KeccakHasher, Keccak};

use crate::hash::hash_types::{BytesHash, RichField};
use crate::hash::hashing::PlonkyPermutation;
use crate::plonk::config::Hasher;

pub const SPONGE_RATE: usize = 8;
pub const SPONGE_CAPACITY: usize = 4;
pub const SPONGE_WIDTH: usize = SPONGE_RATE + SPONGE_CAPACITY;

/// Keccak-256 pseudo-permutation (not necessarily one-to-one) used in the challenger.
/// A state `input: [F; 12]` is sent to the field representation of `H(input) || H(H(input)) || H(H(H(input)))`
/// where `H` is the Keccak-256 hash.
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct KeccakPermutation<F: RichField> {
    state: [F; SPONGE_WIDTH],
}

impl<F: RichField> Eq for KeccakPermutation<F> {}

impl<F: RichField> AsRef<[F]> for KeccakPermutation<F> {
    fn as_ref(&self) -> &[F] {
        &self.state
    }
}

// TODO: Several implementations here are copied from
// PoseidonPermutation; they should be refactored.
impl<F: RichField> PlonkyPermutation<F> for KeccakPermutation<F> {
    const RATE: usize = SPONGE_RATE;
    const WIDTH: usize = SPONGE_WIDTH;

    fn new<I: IntoIterator<Item = F>>(elts: I) -> Self {
        let mut perm = Self {
            state: [F::default(); SPONGE_WIDTH],
        };
        perm.set_from_iter(elts, 0);
        perm
    }

    fn set_elt(&mut self, elt: F, idx: usize) {
        self.state[idx] = elt;
    }

    fn set_from_slice(&mut self, elts: &[F], start_idx: usize) {
        let begin = start_idx;
        let end = start_idx + elts.len();
        self.state[begin..end].copy_from_slice(elts);
    }

    fn set_from_iter<I: IntoIterator<Item = F>>(&mut self, elts: I, start_idx: usize) {
        for (s, e) in self.state[start_idx..].iter_mut().zip(elts) {
            *s = e;
        }
    }

    fn permute(&mut self) {
        const STRIDE: usize = size_of::<u64>();
        let mut state_bytes = vec![0u8; SPONGE_WIDTH * STRIDE];
        for i in 0..SPONGE_WIDTH {
            state_bytes[i * STRIDE..(i + 1) * STRIDE]
                .copy_from_slice(&self.state[i].to_canonical_u64().to_le_bytes());
        }

        let hash_onion = core::iter::repeat_with(|| {
            let output = keccak(state_bytes.clone()).0;
            state_bytes = output.to_vec();
            output
        });

        let hash_onion_u64s = hash_onion.flat_map(|output| {
            output
                .array_chunks::<STRIDE>()
                .copied()
                .map(u64::from_le_bytes)
                .collect_vec()
        });

        // Parse field elements from u64 stream, using rejection sampling such that words that don't
        // fit in F are ignored.
        let mut hash_onion_elems = hash_onion_u64s
            .filter(|&word| word < F::ORDER)
            .map(F::from_canonical_u64);

        self.state = core::array::from_fn(|_| hash_onion_elems.next().unwrap());
    }

    fn squeeze(&self) -> &[F] {
        &self.state[..Self::RATE]
    }
}

/// Keccak-256 hash function.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct KeccakHash<const N: usize>;
impl<F: RichField, const N: usize> Hasher<F> for KeccakHash<N> {
    const HASH_SIZE: usize = N;
    type Hash = BytesHash<N>;
    type Permutation = KeccakPermutation<F>;

    fn hash_no_pad(input: &[F]) -> Self::Hash {
        let mut keccak256 = Keccak::v256();
        for x in input.iter() {
            let b = x.to_canonical_u64().to_le_bytes();
            keccak256.update(&b);
        }
        let mut hash_bytes = [0u8; 32];
        keccak256.finalize(&mut hash_bytes);

        let mut arr = [0; N];
        arr.copy_from_slice(&hash_bytes[..N]);
        BytesHash(arr)
    }

    fn two_to_one(left: Self::Hash, right: Self::Hash) -> Self::Hash {
        let mut keccak256 = Keccak::v256();
        keccak256.update(&left.0);
        keccak256.update(&right.0);

        let mut hash_bytes = [0u8; 32];
        keccak256.finalize(&mut hash_bytes);

        let mut arr = [0; N];
        arr.copy_from_slice(&hash_bytes[..N]);
        BytesHash(arr)
    }
}

pub fn keccak<T: AsRef<[u8]>>(s: T) -> BytesHash<32> {
    let mut keccak256 = Keccak::v256();
    keccak256.update(s.as_ref());

    let mut hash_bytes = [0u8; 32];
    keccak256.finalize(&mut hash_bytes);

    BytesHash(hash_bytes)
}
