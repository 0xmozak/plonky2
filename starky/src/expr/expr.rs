//! Expression tree and Expression Builder
use bumpalo::Bump;

use super::evaluator::{Evaluator, PureEvaluator};
/// Contains a reference to [`ExprTree`] that is managed by [`ExprBuilder`].
#[derive(Clone, Copy, Debug)]
pub enum Expr<'a, V> {
    /// TODO: Add docs
    Basic {
        /// TODO: Add docs
        value: i64,
    },
    /// TODO: Add docs
    Compound {
        /// TODO: Add docs
        expr: CompoundExpr<'a, V>,
        /// TODO: Add docs
        builder: &'a ExprBuilder,
    },
}

impl<'a, V> From<i64> for Expr<'a, V> {
    fn from(value: i64) -> Self {
        Expr::Basic { value }
    }
}

impl<'a, V> Default for Expr<'a, V> {
    fn default() -> Self {
        Expr::from(0)
    }
}

/// Main type to hold expression trees.  Contains Expressions defined on `V`
/// with expression trees that will be alive for at last `'a`.
impl<'a, V> Expr<'a, V> {
    /// TODO: Add docs
    pub fn bin_op(op: BinOp, lhs: Expr<'a, V>, rhs: Expr<'a, V>) -> Expr<'a, V> {
        match (lhs, rhs) {
            (Expr::Basic { value: left }, Expr::Basic { value: right }) => {
                Expr::from(PureEvaluator::default().bin_op(op, left, right))
            }
            (left @ Expr::Compound { builder, .. }, right)
            | (left, right @ Expr::Compound { builder, .. }) => builder.wrap(builder.bin_op(
                op,
                builder.ensure_interned(left),
                builder.ensure_interned(right),
            )),
        }
    }

    /// TODO: Add docs
    pub fn una_op(op: UnaOp, expr: Expr<'a, V>) -> Expr<'a, V> {
        match expr {
            Expr::Basic { value } => Expr::from(PureEvaluator::default().una_op(op, value)),
            Expr::Compound { expr, builder } => builder.wrap(builder.una_op(op, expr)),
        }
    }
}

impl<'a, V> Expr<'a, V> {
    /// TODO: Add docs
    pub fn is_binary(self) -> Self
    where
        V: Copy,
    {
        self * (1 - self)
    }

    /// Reduce a sequence of terms into a single term using powers of `base`.
    pub fn reduce_with_powers<I>(terms: I, base: i64) -> Self
    where
        I: IntoIterator<Item = Self>,
        I::IntoIter: DoubleEndedIterator,
    {
        terms
            .into_iter()
            .rev()
            .fold(Expr::from(0), |acc, term| acc * base + term)
    }
}

/// Expression Builder.  Contains a [`Bump`] memory arena that will allocate and
/// store all the [`ExprTree`]s.
#[derive(Debug, Default)]
pub struct ExprBuilder {
    bump: Bump,
}

impl ExprBuilder {
    /// Internalise an [`ExprTree`] by moving it to memory allocated by the
    /// [`Bump`] arena owned by [`ExprBuilder`].
    fn intern<'a, V>(&'a self, expr_tree: ExprTree<'a, V>) -> CompoundExpr<'a, V> {
        self.bump.alloc(expr_tree).into()
    }

    fn ensure_interned<'a, V>(&'a self, expr: Expr<'a, V>) -> CompoundExpr<'a, V> {
        match expr {
            Expr::Compound { expr, .. } => expr,
            Expr::Basic { value } => self.constant_tree(value),
        }
    }

    /// Wrap [`ExprTree`] reference with an [`Expr`] wrapper
    fn wrap<'a, V>(&'a self, expr: CompoundExpr<'a, V>) -> Expr<'a, V> {
        Expr::Compound {
            expr,
            builder: self,
        }
    }

    /// Convenience method for creating `BinOp` nodes
    fn bin_op<'a, V>(
        &'a self,
        op: BinOp,
        left: CompoundExpr<'a, V>,
        right: CompoundExpr<'a, V>,
    ) -> CompoundExpr<'a, V> {
        let expr_tree = ExprTree::BinOp { op, left, right };
        self.intern(expr_tree)
    }

    /// Convenience method for creating `UnaOp` nodes
    fn una_op<'a, V>(&'a self, op: UnaOp, expr: CompoundExpr<'a, V>) -> CompoundExpr<'a, V> {
        let expr_tree = ExprTree::UnaOp { op, expr };
        self.intern(expr_tree)
    }

    /// Allocate Constant Expression Tree in the Expr Builder
    fn constant_tree<V>(&self, value: i64) -> CompoundExpr<'_, V> {
        self.intern(ExprTree::Constant { value })
    }

    fn lit_tree<V>(&self, value: V) -> CompoundExpr<'_, V> {
        self.intern(ExprTree::Literal { value })
    }

    /// Create a `Constant` expression
    pub fn constant<V>(&self, value: i64) -> Expr<'_, V> {
        self.wrap(self.constant_tree(value))
    }

    /// Create a `Literal` expression
    pub fn lit<V>(&self, value: V) -> Expr<'_, V> {
        self.wrap(self.lit_tree(value))
    }
}

/// Enum for binary operations
#[derive(Debug, Eq, PartialEq, Clone, Copy, Hash)]
pub enum BinOp {
    /// TODO: Add docs
    Add,
    /// TODO: Add docs
    Sub,
    /// TODO: Add docs
    Mul,
}

/// Unary operations
#[derive(Debug, Eq, PartialEq, Clone, Copy, Hash)]
pub enum UnaOp {
    /// TODO: Add docs
    Neg,
}

/// TODO: Add docs
#[derive(Debug, Clone, Copy)]
pub struct CompoundExpr<'a, V>(pub &'a ExprTree<'a, V>);

impl<'a, V> From<&'a ExprTree<'a, V>> for CompoundExpr<'a, V> {
    fn from(value: &'a ExprTree<'a, V>) -> Self {
        CompoundExpr(value)
    }
}

impl<'a, V> From<&'a mut ExprTree<'a, V>> for CompoundExpr<'a, V> {
    fn from(value: &'a mut ExprTree<'a, V>) -> Self {
        CompoundExpr(value)
    }
}

/// Internal type to represent the expression trees
#[derive(Debug)]
pub enum ExprTree<'a, V> {
    /// TODO: Add docs
    BinOp {
        /// TODO: Add docs
        op: BinOp,
        /// TODO: Add docs
        left: CompoundExpr<'a, V>,
        /// TODO: Add docs
        right: CompoundExpr<'a, V>,
    },
    /// TODO: Add docs
    UnaOp {
        /// TODO: Add docs
        op: UnaOp,
        /// TODO: Add docs
        expr: CompoundExpr<'a, V>,
    },
    /// TODO: Add docs
    Literal {
        /// TODO: Add docs
        value: V,
    },
    /// TODO: Add docs
    Constant {
        /// TODO: Add docs
        value: i64,
    },
}
