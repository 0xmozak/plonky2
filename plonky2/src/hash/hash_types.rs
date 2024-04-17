#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
use core::borrow::BorrowMut;

use anyhow::ensure;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::field::goldilocks_field::GoldilocksField;
use crate::field::types::{Field, PrimeField64, Sample};
use crate::hash::poseidon::Poseidon;
use crate::hash::poseidon2::Poseidon2;
use crate::iop::target::Target;
use crate::plonk::config::GenericHashOut;

/// A prime order field with the features we need to use it as a base field in our argument system.
pub trait RichField: PrimeField64 + Poseidon + Poseidon2 {}

impl RichField for GoldilocksField {}

pub const NUM_HASH_OUT_ELTS: usize = 4;

/// Represents a ~256 bit hash output.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct HashOut<F: Field> {
    pub elements: [F; NUM_HASH_OUT_ELTS],
}

impl<F: Field> HashOut<F> {
    pub const ZERO: Self = Self {
        elements: [F::ZERO; NUM_HASH_OUT_ELTS],
    };

    // TODO: Switch to a TryFrom impl.
    pub fn from_vec(elements: Vec<F>) -> Self {
        debug_assert!(elements.len() == NUM_HASH_OUT_ELTS);
        Self {
            elements: elements.try_into().unwrap(),
        }
    }

    pub fn from_partial(elements_in: &[F]) -> Self {
        let mut elements = [F::ZERO; NUM_HASH_OUT_ELTS];
        elements[0..elements_in.len()].copy_from_slice(elements_in);
        Self { elements }
    }
}

impl<F: Field> From<[F; NUM_HASH_OUT_ELTS]> for HashOut<F> {
    fn from(elements: [F; NUM_HASH_OUT_ELTS]) -> Self {
        Self { elements }
    }
}

impl<F: Field> TryFrom<&[F]> for HashOut<F> {
    type Error = anyhow::Error;

    fn try_from(elements: &[F]) -> Result<Self, Self::Error> {
        ensure!(elements.len() == NUM_HASH_OUT_ELTS);
        Ok(Self {
            elements: elements.try_into().unwrap(),
        })
    }
}

impl<F> Sample for HashOut<F>
where
    F: Field,
{
    #[inline]
    fn sample<R>(rng: &mut R) -> Self
    where
        R: rand::RngCore + ?Sized,
    {
        Self {
            elements: [
                F::sample(rng),
                F::sample(rng),
                F::sample(rng),
                F::sample(rng),
            ],
        }
    }
}

impl<F: RichField> GenericHashOut<F> for HashOut<F> {
    fn to_bytes(self) -> impl AsRef<[u8]> + AsMut<[u8]> + BorrowMut<[u8]> + Copy {
        let mut bytes = [0u8; NUM_HASH_OUT_ELTS * 8];
        for (i, x) in self.elements.into_iter().enumerate() {
            let i = i * 8;
            bytes[i..i + 8].copy_from_slice(&x.to_canonical_u64().to_le_bytes())
        }
        bytes
    }

    fn from_bytes(bytes: &[u8]) -> Self {
        let mut bytes = bytes
            .chunks(8)
            .take(NUM_HASH_OUT_ELTS)
            .map(|x| F::from_canonical_u64(u64::from_le_bytes(x.try_into().unwrap())));
        HashOut {
            elements: [(); NUM_HASH_OUT_ELTS].map(|()| bytes.next().unwrap()),
        }
    }

    fn from_byte_iter(mut bytes: impl Iterator<Item = u8>) -> Self {
        let bytes = [[(); 8]; NUM_HASH_OUT_ELTS].map(|b| b.map(|()| bytes.next().unwrap()));

        HashOut {
            elements: bytes.map(|x| F::from_canonical_u64(u64::from_le_bytes(x))),
        }
    }

    fn from_iter(mut inputs: impl Iterator<Item = F>) -> Self {
        HashOut {
            elements: [(); NUM_HASH_OUT_ELTS].map(|()| inputs.next().unwrap()),
        }
    }

    fn into_iter(self) -> impl Iterator<Item = F> {
        self.elements.into_iter()
    }
}

impl<F: Field> Default for HashOut<F> {
    fn default() -> Self {
        Self::ZERO
    }
}

/// Represents a ~256 bit hash output.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct HashOutTarget {
    pub elements: [Target; NUM_HASH_OUT_ELTS],
}

impl HashOutTarget {
    // TODO: Switch to a TryFrom impl.
    pub fn from_vec(elements: Vec<Target>) -> Self {
        debug_assert!(elements.len() == NUM_HASH_OUT_ELTS);
        Self {
            elements: elements.try_into().unwrap(),
        }
    }

    pub fn from_partial(elements_in: &[Target], zero: Target) -> Self {
        let mut elements = [zero; NUM_HASH_OUT_ELTS];
        elements[0..elements_in.len()].copy_from_slice(elements_in);
        Self { elements }
    }
}

impl From<[Target; NUM_HASH_OUT_ELTS]> for HashOutTarget {
    fn from(elements: [Target; NUM_HASH_OUT_ELTS]) -> Self {
        Self { elements }
    }
}

impl TryFrom<&[Target]> for HashOutTarget {
    type Error = anyhow::Error;

    fn try_from(elements: &[Target]) -> Result<Self, Self::Error> {
        ensure!(elements.len() == NUM_HASH_OUT_ELTS);
        Ok(Self {
            elements: elements.try_into().unwrap(),
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MerkleCapTarget(pub Vec<HashOutTarget>);

/// Hash consisting of a byte array.
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub struct BytesHash<const N: usize>(pub [u8; N]);

impl<const N: usize> Sample for BytesHash<N> {
    #[inline]
    fn sample<R>(rng: &mut R) -> Self
    where
        R: rand::RngCore + ?Sized,
    {
        let mut buf = [0; N];
        rng.fill_bytes(&mut buf);
        Self(buf)
    }
}

impl<F: RichField, const N: usize> GenericHashOut<F> for BytesHash<N> {
    fn to_bytes(self) -> impl AsRef<[u8]> + AsMut<[u8]> + BorrowMut<[u8]> + Copy {
        self.0
    }

    fn from_bytes(bytes: &[u8]) -> Self {
        Self(bytes.try_into().unwrap())
    }

    fn from_byte_iter(mut bytes: impl Iterator<Item = u8>) -> Self {
        Self(core::array::from_fn(|_| bytes.next().unwrap()))
    }

    fn into_iter(self) -> impl Iterator<Item = F> {
        // Chunks of 7 bytes since 8 bytes would allow collisions.
        const STRIDE: usize = 7;

        (0..N).step_by(STRIDE).map(move |i| {
            let mut bytes = &self.0[i..];
            if bytes.len() > STRIDE {
                bytes = &bytes[..STRIDE];
            }
            let mut arr = [0; 8];
            arr[..bytes.len()].copy_from_slice(bytes);
            F::from_canonical_u64(u64::from_le_bytes(arr))
        })
    }
}

impl<const N: usize> Serialize for BytesHash<N> {
    fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        todo!()
    }
}

impl<'de, const N: usize> Deserialize<'de> for BytesHash<N> {
    fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        todo!()
    }
}
