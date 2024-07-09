//! `StarkFrame` whose `View` and `PublicInputs` are wrapped in type constructors.
use super::{Expr, ExprBuilder};
use crate::evaluation_frame::{StarkEvaluationFrame, StarkFrame};

/// A helper around `StarkFrame` to add types
#[derive(Debug)]
pub struct StarkFrameTyped<View, PublicInputs> {
    /// TODO: Add docs
    pub local_values: View,
    /// TODO: Add docs
    pub next_values: View,
    /// TODO: Add docs
    pub public_inputs: PublicInputs,
}

impl<View, PublicInputs> StarkFrameTyped<View, PublicInputs> {
    /// TODO: Add docs
    pub fn from_values<T, U>(lv: &[T], nv: &[T], pis: &[U]) -> Self
    where
        T: Copy,
        U: Copy,
        View: FromIterator<T>,
        PublicInputs: FromIterator<U>,
    {
        Self {
            local_values: lv.iter().copied().collect(),
            next_values: nv.iter().copied().collect(),
            public_inputs: pis.iter().copied().collect(),
        }
    }

    /// TODO: Add docs
    pub fn map_view<T, B, F, MappedView>(
        self,
        mut f: F,
    ) -> StarkFrameTyped<MappedView, PublicInputs>
    where
        View: IntoIterator<Item = T>,
        MappedView: FromIterator<B>,
        F: FnMut(T) -> B,
    {
        StarkFrameTyped {
            local_values: self.local_values.into_iter().map(&mut f).collect(),
            next_values: self.next_values.into_iter().map(f).collect(),
            public_inputs: self.public_inputs,
        }
    }

    /// TODO: Add docs
    pub fn map_public_inputs<U, C, F, MappedPublicInputs>(
        self,
        f: F,
    ) -> StarkFrameTyped<View, MappedPublicInputs>
    where
        PublicInputs: IntoIterator<Item = U>,
        MappedPublicInputs: FromIterator<C>,
        F: FnMut(U) -> C,
    {
        StarkFrameTyped {
            local_values: self.local_values,
            next_values: self.next_values,
            public_inputs: self.public_inputs.into_iter().map(f).collect(),
        }
    }
}

impl<'a, T, U, const N: usize, const N2: usize, View, PublicInputs>
    From<&'a StarkFrame<T, U, N, N2>> for StarkFrameTyped<View, PublicInputs>
where
    T: Copy + Default,
    U: Copy + Default,
    View: From<[T; N]> + FromIterator<T>,
    PublicInputs: From<[U; N2]> + FromIterator<U>,
{
    fn from(value: &'a StarkFrame<T, U, N, N2>) -> Self {
        Self::from_values(
            value.get_local_values(),
            value.get_next_values(),
            value.get_public_inputs(),
        )
    }
}

impl ExprBuilder {
    /// Convert from untyped `StarkFrame` to a typed representation.
    ///
    /// We ignore public inputs for now, and leave them as is.
    pub fn to_typed_starkframe<'a, T, U, const N: usize, const N2: usize, View, PublicInputs>(
        &'a self,
        vars: &'a StarkFrame<T, U, N, N2>,
    ) -> StarkFrameTyped<View, PublicInputs>
    where
        T: Copy + Clone + Default + From<U>,
        U: Copy + Clone + Default,
        // We don't actually need the first constraint, but it's useful to make the compiler yell
        // at us, if we mix things up. See the TODO about fixing `StarkEvaluationFrame` to
        // give direct access to its contents.
        View: FromIterator<Expr<'a, T>>,
        PublicInputs: FromIterator<Expr<'a, T>>,
    {
        // NOTE: Rust needs to know all the intermediate types
        let frame: StarkFrameTyped<Vec<T>, Vec<U>> = StarkFrameTyped::from(vars);
        let frame: StarkFrameTyped<Vec<T>, Vec<T>> = frame.map_public_inputs(|v| T::from(v));
        self.inject_starkframe(frame)
    }

    /// Inject `StarkFrameTypes` into the `ExprBuilder`.
    ///
    /// This function will decompose `StarkFrameTyped` using the `IntoIterator`
    /// instances of `View` and `PublicInputs` and then recompose them back
    /// using `FromIterator` instances of `MappedView` and `MappedPublicInputs`
    /// respectively.
    pub fn inject_starkframe<'a, T: 'a, U: 'a, View, PublicInputs, MappedView, MappedPublicInputs>(
        &'a self,
        frame: StarkFrameTyped<View, PublicInputs>,
    ) -> StarkFrameTyped<MappedView, MappedPublicInputs>
    where
        View: IntoIterator<Item = T>,
        PublicInputs: IntoIterator<Item = U>,
        MappedView: FromIterator<Expr<'a, T>>,
        MappedPublicInputs: FromIterator<Expr<'a, U>>,
    {
        frame
            .map_view(|v| self.lit(v))
            .map_public_inputs(|v| self.lit(v))
    }
}
