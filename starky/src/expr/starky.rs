//! Starky-specific functionality

use core::fmt::Debug;
use std::fmt::Display;
use std::marker::{Copy, PhantomData};
use std::panic::Location;

use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::field::packed::PackedField;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;

pub use super::PureEvaluator;
use super::{BinOp, Caching, Evaluator, Expr, ExprBuilder, UnaOp};
use crate::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};
use crate::evaluation_frame::{StarkEvaluationFrame, StarkFrame};
use crate::stark::Stark;

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

struct CircuitBuilderEvaluator<'a, F, const D: usize>
where
    F: RichField,
    F: Extendable<D>,
{
    builder: &'a mut CircuitBuilder<F, D>,
}

impl<'a, F, const D: usize> Evaluator<'a, ExtensionTarget<D>> for CircuitBuilderEvaluator<'a, F, D>
where
    F: RichField,
    F: Extendable<D>,
{
    fn bin_op(
        &mut self,
        op: BinOp,
        left: ExtensionTarget<D>,
        right: ExtensionTarget<D>,
    ) -> ExtensionTarget<D> {
        match op {
            BinOp::Add => self.builder.add_extension(left, right),
            BinOp::Sub => self.builder.sub_extension(left, right),
            BinOp::Mul => self.builder.mul_extension(left, right),
        }
    }

    fn una_op(&mut self, op: UnaOp, expr: ExtensionTarget<D>) -> ExtensionTarget<D> {
        match op {
            UnaOp::Neg => {
                let neg_one = self.builder.neg_one();
                self.builder.scalar_mul_ext(neg_one, expr)
            }
        }
    }

    fn constant(&mut self, value: i64) -> ExtensionTarget<D> {
        let f = F::from_noncanonical_i64(value);
        self.builder.constant_extension(f.into())
    }
}

/// TODO: Add docs
#[must_use]
pub fn packed_field_evaluator<F, FE, P, const D: usize, const D2: usize>() -> PureEvaluator<P>
where
    F: RichField,
    F: Extendable<D>,
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    fn convert<F, FE, P, const D: usize, const D2: usize>(value: i64) -> P
    where
        F: RichField,
        F: Extendable<D>,
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>,
    {
        P::from(FE::from_noncanonical_i64(value))
    }
    PureEvaluator(convert)
}

/// TODO: Add docs
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Constraint<E> {
    /// TODO: Add docs
    pub constraint_type: ConstraintType,
    /// TODO: Add docs
    pub location: &'static Location<'static>,
    /// TODO: Add docs
    pub term: E,
}

impl<E> Constraint<E> {
    fn map<B, F>(self, mut f: F) -> Constraint<B>
    where
        F: FnMut(E) -> B,
    {
        Constraint {
            constraint_type: self.constraint_type,
            location: self.location,
            term: f(self.term),
        }
    }
}

/// TODO: Add docs
#[derive(PartialEq, Eq, PartialOrd, Ord, Default, Debug)]
pub enum ConstraintType {
    /// TODO: Add docs
    FirstRow,
    #[default]
    /// TODO: Add docs
    Always,
    /// TODO: Add docs
    Transition,
    /// TODO: Add docs
    LastRow,
}

/// TODO: Add docs
#[derive(Debug, Default)]
pub struct ConstraintBuilder<E> {
    constraints: Vec<Constraint<E>>,
}

impl<E> From<Vec<Constraint<E>>> for ConstraintBuilder<E> {
    fn from(constraints: Vec<Constraint<E>>) -> Self {
        Self { constraints }
    }
}

impl<E> ConstraintBuilder<E> {
    #[track_caller]
    fn constraint(&mut self, term: E, constraint_type: ConstraintType) {
        self.constraints.push(Constraint {
            constraint_type,
            location: Location::caller(),
            term,
        });
    }

    /// TODO: Add docs
    #[track_caller]
    pub fn first_row(&mut self, constraint: E) {
        self.constraint(constraint, ConstraintType::FirstRow);
    }

    /// TODO: Add docs
    #[track_caller]
    pub fn last_row(&mut self, constraint: E) {
        self.constraint(constraint, ConstraintType::LastRow);
    }

    /// TODO: Add docs
    #[track_caller]
    pub fn always(&mut self, constraint: E) {
        self.constraint(constraint, ConstraintType::Always);
    }

    /// TODO: Add docs
    #[track_caller]
    pub fn transition(&mut self, constraint: E) {
        self.constraint(constraint, ConstraintType::Transition);
    }
}

/// TODO: Add docs
pub fn build_ext<F, const D: usize>(
    cb: ConstraintBuilder<Expr<'_, ExtensionTarget<D>>>,
    circuit_builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
) where
    F: RichField,
    F: Extendable<D>,
{
    for constraint in cb.constraints {
        let mut evaluator = Caching::from(CircuitBuilderEvaluator {
            builder: circuit_builder,
        });
        let constraint = constraint.map(|constraint| evaluator.eval(constraint));
        (match constraint.constraint_type {
            ConstraintType::FirstRow => RecursiveConstraintConsumer::constraint_first_row,
            ConstraintType::Always => RecursiveConstraintConsumer::constraint,
            ConstraintType::Transition => RecursiveConstraintConsumer::constraint_transition,
            ConstraintType::LastRow => RecursiveConstraintConsumer::constraint_last_row,
        })(yield_constr, circuit_builder, constraint.term);
    }
}

/// TODO: Add docs
#[must_use]
pub fn build_debug<F, FE, P, const D: usize, const D2: usize>(
    cb: ConstraintBuilder<Expr<'_, P>>,
) -> Vec<Constraint<P>>
where
    F: RichField,
    F: Extendable<D>,
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    let mut evaluator = Caching::from(packed_field_evaluator());
    cb.constraints
        .into_iter()
        .map(|c| c.map(|constraint| evaluator.eval(constraint)))
        .collect()
}

/// TODO: Add docs
pub fn build_packed<F, FE, P, const D: usize, const D2: usize>(
    cb: ConstraintBuilder<Expr<'_, P>>,
    yield_constr: &mut ConstraintConsumer<P>,
) where
    F: RichField,
    F: Extendable<D>,
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    let mut evaluator = Caching::from(packed_field_evaluator());
    let evaluated = cb
        .constraints
        .into_iter()
        .map(|c| c.map(|constraint| evaluator.eval(constraint)))
        .collect::<Vec<_>>();

    for c in evaluated {
        (match c.constraint_type {
            ConstraintType::FirstRow => ConstraintConsumer::constraint_first_row,
            ConstraintType::Always => ConstraintConsumer::constraint,
            ConstraintType::Transition => ConstraintConsumer::constraint_transition,
            ConstraintType::LastRow => ConstraintConsumer::constraint_last_row,
        })(yield_constr, c.term);
    }
}

/// Convenience alias to `G::PublicInputs<T>`.
pub type PublicInputsOf<G, T, const COLUMNS: usize, const PUBLIC_INPUTS: usize> =
    <G as GenerateConstraints<COLUMNS, PUBLIC_INPUTS>>::PublicInputs<T>;

/// Convenience alias to `G::View<T>`.
pub type ViewOf<G, T, const COLUMNS: usize, const PUBLIC_INPUTS: usize> =
    <G as GenerateConstraints<COLUMNS, PUBLIC_INPUTS>>::View<T>;

/// Convenience alias to `StarkFrameTyped` that will be defined over
/// `G::View<Expr<'a, T>>` and `G::PublicInputs<Expr<'a, T>>`
pub type Vars<'a, G, T, const COLUMNS: usize, const PUBLIC_INPUTS: usize> = StarkFrameTyped<
    ViewOf<G, Expr<'a, T>, COLUMNS, PUBLIC_INPUTS>,
    PublicInputsOf<G, Expr<'a, T>, COLUMNS, PUBLIC_INPUTS>,
>;

/// Trait for generating constraints independently from the type of the field
/// and independently from the API of the proving system.
pub trait GenerateConstraints<const COLUMNS: usize, const PUBLIC_INPUTS: usize> {
    /// TODO: Add docs
    type View<E: Debug>: From<[E; COLUMNS]> + FromIterator<E>;
    /// TODO: Add docs
    type PublicInputs<E: Debug>: From<[E; PUBLIC_INPUTS]> + FromIterator<E>;

    /// TODO: Add docs
    fn generate_constraints<'a, T: Copy + Debug>(
        &self,
        _vars: &Vars<'a, Self, T, COLUMNS, PUBLIC_INPUTS>,
    ) -> ConstraintBuilder<Expr<'a, T>> {
        ConstraintBuilder::default()
    }
}

/// TODO: Add docs
#[derive(Copy, Clone, Debug, Default)]
pub struct StarkFrom<F, G, const D: usize, const COLUMNS: usize, const PUBLIC_INPUTS: usize> {
    /// TODO: Add docs
    pub witness: G,
    /// TODO: Add docs
    pub _f: PhantomData<F>,
}

impl<G: Display, F, const D: usize, const COLUMNS: usize, const PUBLIC_INPUTS: usize> Display
    for StarkFrom<F, G, D, COLUMNS, PUBLIC_INPUTS>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.witness.fmt(f)
    }
}

impl<G, F, const D: usize, const COLUMNS: usize, const PUBLIC_INPUTS: usize> Stark<F, D>
    for StarkFrom<F, G, D, COLUMNS, PUBLIC_INPUTS>
where
    G: Sync + GenerateConstraints<COLUMNS, PUBLIC_INPUTS> + Copy,
    F: RichField + Extendable<D> + Debug,
{
    type EvaluationFrame<FE, P, const D2: usize> = StarkFrame<P, P::Scalar, { COLUMNS }, { PUBLIC_INPUTS }>

    where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>;
    type EvaluationFrameTarget =
        StarkFrame<ExtensionTarget<D>, ExtensionTarget<D>, { COLUMNS }, { PUBLIC_INPUTS }>;

    fn eval_packed_generic<FE, P, const D2: usize>(
        &self,
        vars: &Self::EvaluationFrame<FE, P, D2>,
        constraint_consumer: &mut ConstraintConsumer<P>,
    ) where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE> + Debug + Copy,
    {
        let expr_builder = ExprBuilder::default();
        let constraints = self
            .witness
            .generate_constraints::<_>(&expr_builder.to_typed_starkframe(vars));
        build_packed(constraints, constraint_consumer);
    }

    fn eval_ext_circuit(
        &self,
        circuit_builder: &mut CircuitBuilder<F, D>,
        vars: &Self::EvaluationFrameTarget,
        constraint_consumer: &mut RecursiveConstraintConsumer<F, D>,
    ) {
        let expr_builder = ExprBuilder::default();
        let constraints = self
            .witness
            .generate_constraints(&expr_builder.to_typed_starkframe(vars));
        build_ext(constraints, circuit_builder, constraint_consumer);
    }

    fn constraint_degree(&self) -> usize {
        3
    }
}
