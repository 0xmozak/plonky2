//! Simple library for handling ASTs for polynomials for ZKP in Rust
//!
//! NOTE: so far Expr type _belonged_ to Expr builder.  It could even be
//! considered a singleton type per each expression instance.  However, now we
//! want to relax that requirement, and have some expressions that are not tied
//! to expression builders, so that we can have Default instance for
//! expressions.
//!
//! The current API provided by Expr type are the trait instances, which are
//!
//! - [`Add`]
//!   - [`Expr`] + [`Expr`]
//!   - [`i64`] + [`Expr`]
//!   - [`Expr`] + [`i64`]
//! - [`Sub`]
//!   - [`Expr`] - [`Expr`]
//!   - [`i64`] - [`Expr`]
//!   - [`Expr`] - [`i64`]
//! - [`Mul`]
//!   - [`Expr`] * [`Expr`]
//!   - [`i64`] * [`Expr`]
//!   - [`Expr`] * [`i64`]
//! - [`Neg`]
//!   - (- [`Expr`])
//!
//! Then, the current API for Expr builder was pretty much the ability to inject
//! `V` and i64 into Exprs
//!
//! - (private) intern for internalising ExprTree
//! - (private) binop helper method
//! - (private) unop helper method
//! - lit for V
//! - constant for i64
//! - helper methods
//!   - add
//!   - sub
//!   - mul
//!   - neg
//!
//! There is a private contract between ExprBuilder and Expr, as Expr is just a
//! wrapper around ExprTree provided by ExprBuilder, as builder internally
//! operates on ExprTree.
//!
//! Ideally, we want to provide a basic implementation of ExprBuilder for our
//! end users to extend, but I am not sure how to do that efficiently in Rust
//! yet.
//!
//! I also noticed that sometimes it is easier to extend the Expr type, rather
//! than ExprBuilder.
//!
//! Finally, there is the case of Evaluators, because they do form a contract
//! with internal ExprTree, as they provide the semantics for the operations.
//!
//! # TODO
//!
//! - [ ] TODO: support `|` via multiplication.
//! - [ ] TODO support `&` via distributive law, and integration with constraint
//! builder. (a & b) | c == (a | c) & (b | c) == [(a | c), (b | c)] where [..]
//! means split into multiple constraints.

pub mod evaluator;
pub use evaluator::*;
pub mod expr;
pub use expr::*;
pub mod ops;
pub mod starky;

#[cfg(test)]
mod tests {
    use super::evaluator::*;
    use super::*;

    #[test]
    fn it_works() {
        let expr = ExprBuilder::default();

        let a = expr.lit(7i64);
        let b = expr.lit(5i64);

        let mut p = PureEvaluator::default();

        assert_eq!(p.eval(a + b), 12);
        assert_eq!(p.eval(a - b), 2);
        assert_eq!(p.eval(a * b), 35);
    }

    #[test]
    fn it_works_assign() {
        let expr = ExprBuilder::default();

        let a = expr.lit(7i64);
        let b = expr.lit(5i64);
        let mut c = expr.lit(0i64);

        let mut p = PureEvaluator::default();

        c += a + b;
        assert_eq!(p.eval(c), 12);
        c -= b;
        assert_eq!(p.eval(c), 7);
        c *= b;
        assert_eq!(p.eval(c), 35);
    }

    #[test]
    fn basic_expressions_work() {
        let expr = ExprBuilder::default();

        let a = expr.lit(7_i64);
        let b = expr.lit(5_i64);

        let c: Expr<'_, i64> = Expr::from(3);

        let mut p = PureEvaluator::default();

        assert_eq!(p.eval(a + b * c), 22);
        assert_eq!(p.eval(a - b * c), -8);
        assert_eq!(p.eval(a * b * c), 105);
    }

    #[test]
    fn basic_expressions_with_no_annotations() {
        let a: Expr<'_, i64> = Expr::from(7);
        let b = Expr::from(5);
        let c = Expr::from(3);

        let mut p = PureEvaluator::default();

        assert_eq!(p.eval(a + b * c), 22);
        assert_eq!(p.eval(a - b * c), -8);
        assert_eq!(p.eval(a * b * c), 105);
    }

    #[test]
    fn basic_caching_expressions() {
        let a: Expr<'_, i64> = Expr::from(7);
        let b = Expr::from(5);
        let c = Expr::from(3);

        let mut p = Caching::from(PureEvaluator::default());

        assert_eq!(p.eval(a + b * c), 22);
        assert_eq!(p.eval(a - b * c), -8);
        assert_eq!(p.eval(a * b * c), 105);
    }

    #[test]
    fn count_depth() {
        let eb = ExprBuilder::default();

        let mut c = Counting::<PureEvaluator<_>>::default();
        let mut one = eb.lit(1i64);

        assert_eq!(c.eval(one), 1);
        assert_eq!(c.count(), 0);
        c.reset();

        for _ in 0..10 {
            one = one * one;
        }

        assert_eq!(c.eval(one), 1);
        assert_eq!(c.count(), 1023);
        c.reset();

        let mut c = Caching::from(c);
        assert_eq!(c.eval(one), 1);
        assert_eq!(c.evaluator.count(), 10);
    }

    #[test]
    fn avoids_exponential_blowup() {
        let eb = ExprBuilder::default();
        let mut one = eb.lit(1i64);
        // This should timout most modern machines if executed without caching
        for _ in 0..64 {
            one = one * one;
        }

        let mut p = Caching::<i64, Counting<PureEvaluator<_>>>::default();
        assert_eq!(p.eval(one), 1);
        assert_eq!(p.evaluator.count(), 64);
    }
}
