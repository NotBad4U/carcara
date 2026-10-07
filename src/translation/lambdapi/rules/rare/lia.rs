//! Scripts for the arithmetic RARE rewrites and the arithmetic cases of cvc5's
//! `evaluate`. Mirrors `alethe-lp/rare/lia.lp`.

use super::RareStep;
use crate::translation::lambdapi::*;

/// Provide a proof term for `evaluate` rule that fold numeric constant.
/// For example:
/// ```text
/// (step ti (cl (= (* -16 1) -16)) :rule rare_rewrite :args ("evaluate"))
/// ```
pub(super) fn translate_evaluate_eq_arith() -> Vec<ProofStep> {
    lambdapi! {
        simplify;
        reflexivity;
    }
}


/// In Alethe, `arith_poly_norm` is the arithmetical polynomial normalization rule.
/// It is used to justify steps where an arithmetic expression (a polynomial over integers, rationals, or reals) is rewritten into a canonical, normalized polynomial form. This usually involves:
///   * Flattening nested additions and multiplications
///   * Sorting terms in a fixed order (e.g., lexicographically by variable)
///   * Combining like terms (e.g., 2x + 3x → 5x)
///   * Normalizing coefficients (for rationals, ensuring a canonical denominator)
///   * Eliminating redundant constants or zero terms (e.g., x + 0 → x)
///
/// So, if a proof line in Alethe has justification `:rule arith_poly_norm`, it means the term was transformed into its canonical polynomial representation.
/// This ensures that arithmetic equalities like:
/// ```text
/// (x + 1) + (2*x - 3) ≡ 3*x - 2
/// ```
///
/// The proof is by reflection with `lia.lp`'s `poly_norm_eq`, which reifies the
/// right side in the atom environment of the left one (otherwise `x + y ≡ y + x`
/// would not normalise to the same polynomial). Its premise holds by
/// conversion, and both sides are found by unification with the goal:
///
/// ```text
/// have t50_t3 : π̇ (e1 = e2) ⸬ □) {
///     apply ∨ᵢ₁;
///     apply poly_norm_eq;
///     reflexivity;
/// };
/// ```
pub(super) fn translate_arith_poly_norm(_: &RareStep<'_>) -> Vec<ProofStep> {
    poly_norm_steps()
}

/// The normalisation script itself, on an equality of two polynomials;
/// `rules::lia` re-exports it for `poly_simp`.
pub(crate) fn poly_norm_steps() -> Vec<ProofStep> {
    lambdapi! {
        apply "poly_norm_eq";
        reflexivity;
    }
}
