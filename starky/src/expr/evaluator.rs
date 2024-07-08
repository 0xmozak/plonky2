//! Evaluators

use core::ops::{Add, Mul, Neg, Sub};
use std::collections::HashMap;

use super::{BinOp, CompoundExpr, Expr, ExprTree, UnaOp};

/// Evaluator that can evaluate [`Expr`] to `V`.
pub trait Evaluator<'a, V>
where
    V: Copy,
{
    /// TODO: Add docs
    fn bin_op(&mut self, op: BinOp, left: V, right: V) -> V;
    /// TODO: Add docs
    fn una_op(&mut self, op: UnaOp, expr: V) -> V;
    /// TODO: Add docs
    fn constant(&mut self, value: i64) -> V;
    /// TODO: Add docs
    fn expr_tree(&mut self, expr_tree: &'a ExprTree<'a, V>) -> V {
        match expr_tree {
            ExprTree::BinOp { op, left, right } => {
                let left = self.compound_expr(*left);
                let right = self.compound_expr(*right);
                self.bin_op(*op, left, right)
            }
            ExprTree::UnaOp { op, expr } => {
                let expr = self.compound_expr(*expr);
                self.una_op(*op, expr)
            }
            ExprTree::Literal { value } => *value,
            ExprTree::Constant { value } => self.constant(*value),
        }
    }
    /// TODO: Add docs
    fn compound_expr(&mut self, expr: CompoundExpr<'a, V>) -> V {
        self.expr_tree(expr.0)
    }
    /// TODO: Add docs
    fn eval(&mut self, expr: Expr<'a, V>) -> V {
        match expr {
            Expr::Basic { value } => self.constant(value),
            Expr::Compound { expr, builder: _ } => self.compound_expr(expr),
        }
    }
}

/// Default evaluator for pure values.
#[derive(Debug)]
pub struct PureEvaluator<P>(pub fn(i64) -> P);

// impl<P> Debug for PureEvaluator<P> {
//     // TODO: Add the name of the type
//     fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
//         f.debug_tuple("PureEvaluator").finish()
//     }
// }

impl<'a, V> Evaluator<'a, V> for PureEvaluator<V>
where
    V: Copy + Add<Output = V> + Neg<Output = V> + Mul<Output = V> + Sub<Output = V>,
{
    fn bin_op(&mut self, op: BinOp, left: V, right: V) -> V {
        match op {
            BinOp::Add => left + right,
            BinOp::Sub => left - right,
            BinOp::Mul => left * right,
        }
    }

    fn una_op(&mut self, op: UnaOp, expr: V) -> V {
        match op {
            UnaOp::Neg => -expr,
        }
    }

    fn constant(&mut self, value: i64) -> V {
        (self.0)(value)
    }
}

impl<V> Default for PureEvaluator<V>
where
    V: Copy + Add<Output = V> + Neg<Output = V> + Mul<Output = V> + Sub<Output = V> + From<i64>,
{
    fn default() -> Self {
        Self(V::from)
    }
}

/// TODO: Add docs
#[derive(Debug, Default)]
pub struct Caching<'a, V, E> {
    constant_cache: HashMap<i64, V>,
    value_cache: HashMap<*const ExprTree<'a, V>, V>,
    /// Inner evaluator
    pub evaluator: E,
}

impl<'a, V, E> From<E> for Caching<'a, V, E>
where
    E: Evaluator<'a, V>,
    V: Copy,
{
    fn from(evaluator: E) -> Self {
        Caching {
            constant_cache: HashMap::default(),
            value_cache: HashMap::default(),
            evaluator,
        }
    }
}

impl<'a, V, E> Evaluator<'a, V> for Caching<'a, V, E>
where
    V: Copy,
    E: Evaluator<'a, V>,
{
    fn bin_op(&mut self, op: BinOp, left: V, right: V) -> V {
        self.evaluator.bin_op(op, left, right)
    }

    fn una_op(&mut self, op: UnaOp, expr: V) -> V {
        self.evaluator.una_op(op, expr)
    }

    fn constant(&mut self, k: i64) -> V {
        *self
            .constant_cache
            .entry(k)
            .or_insert_with(|| self.evaluator.constant(k))
    }

    // NOTE: We disable clippy warning about map entry becasue it is impossible
    // to implement the following function using entry(k).or_insert_with, due to
    // the closue argument to or_insert_with needing to mutably borrow self for
    // expr_tree, which would be already mutably borrowed by
    // self.value_cache.entry.
    #[allow(clippy::map_entry)]
    fn compound_expr(&mut self, expr: CompoundExpr<'a, V>) -> V {
        let expr_tree = expr.0;
        let k = expr_tree as *const ExprTree<'_, V>;

        if !self.value_cache.contains_key(&k) {
            let v = self.expr_tree(expr_tree);
            self.value_cache.insert(k, v);
        }

        *self.value_cache.get(&k).unwrap()
    }
}

/// Example evaluator that counts operations
#[derive(Debug, Default)]
pub struct Counting<E> {
    count: u64,
    evaluator: E,
}

impl<E> Counting<E> {
    fn inc(&mut self) {
        self.count += 1;
    }

    /// TODO: Add docs
    pub fn count(&self) -> u64 {
        self.count
    }

    /// TODO: Add docs
    pub fn reset(&mut self) {
        self.count = 0;
    }
}

impl<'a, V, E> Evaluator<'a, V> for Counting<E>
where
    E: Evaluator<'a, V>,
    V: Copy,
{
    fn bin_op(&mut self, op: BinOp, left: V, right: V) -> V {
        self.inc();
        self.evaluator.bin_op(op, left, right)
    }

    fn una_op(&mut self, op: UnaOp, expr: V) -> V {
        self.inc();
        self.evaluator.una_op(op, expr)
    }

    fn constant(&mut self, value: i64) -> V {
        self.inc();
        self.evaluator.constant(value)
    }
}
