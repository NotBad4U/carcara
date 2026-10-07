//! Scripts for the arithmetic RARE rewrites and the arithmetic cases of cvc5's
//! `evaluate`. Mirrors `alethe-lp/rare/lia.lp`.

use super::RareStep;
use crate::translation::lambdapi::*;
use crate::ast::{Rc, Term as AletheTerm, match_term};

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
/// We then would like to produce the script that re-use the normalise for `la_generic`.
/// Note that we need to reify left side first to re-use the reification map for the right side.
/// Otherwise, we can not prove the equality of expression such as `x + y ≡ y + x` because the reification map would be different (l = [x |-> 0, x |-> 1], r = [x |-> 1, x |-> 0]).
///
/// ```text
/// have t50_t3 : π̇ (e1 = e2) ⸬ □) {
///     apply ∨ᵢ₁;
///     rewrite left  .[x in x = _] reify_correct;
///     set l ≔ (reify e1);
///     rewrite .[x in val x = _] eta_prod;
///     rewrite left .[x in _ = x] (reify_correct_withenv (l ₂));
///     rewrite .[x in _ = val x] eta_prod;
///     rewrite left .[x in x = _] norm_correct;
///     rewrite left .[x in _ = x] norm_correct;
///     reflexivity;
/// };
/// ```
pub(super) fn translate_arith_poly_norm(&RareStep { clause, .. }: &RareStep<'_>) -> Vec<ProofStep> {
    let (left, _) = match_term!((= l r) = clause[0]).expect("no equality");
    crate::translation::lambdapi::rules::lia::poly_norm_steps(left)
}

/// The normalisation script itself, on an equality whose left-hand side is
/// `left`; `rules::lia` re-exports it for `poly_simp`.
pub(crate) fn poly_norm_steps(left: &Rc<AletheTerm>) -> Vec<ProofStep> {
    let mut proof = vec![];

    let l_set_id = "l";

    // Encode: rewrite left  .[x in x = _] reify_correct;
    proof.push(ProofStep::Rewrite(
        true,
        Some("[x in x = _]".into()),
        Term::from("reify_correct"),
        vec![],
        SubProofs(None),
    ));

    // Encode: set l ≔ (reify e1);
    let e1: Term = Term::Terms(vec!["reify".into(), left.into()]);
    proof.push(ProofStep::Set(l_set_id.to_owned(), e1));

    // Encode: rewrite .[x in val x = _] eta_prod;
    proof.push(ProofStep::Rewrite(
        false,
        Some("[x in val x = _]".into()),
        Term::from("eta_prod"),
        vec![],
        SubProofs(None),
    ));

    // Encode: rewrite left .[x in _ = x] (reify_correct_withenv (l ₂));
    proof.push(ProofStep::Rewrite(
        true,
        Some("[x in _ = x]".into()),
        Term::from("reify_correct_withenv"),
        vec![Term::from(format!("({} ₂)", l_set_id))],
        SubProofs(None),
    ));

    // Encode: rewrite .[x in _ = val x] eta_prod;
    proof.push(ProofStep::Rewrite(
        false,
        Some("[x in _ = val x]".into()),
        Term::from("eta_prod"),
        vec![],
        SubProofs(None),
    ));

    // Encode: rewrite left  .[x in x = _] norm_correct;
    proof.push(ProofStep::Rewrite(
        true,
        Some("[x in x = _]".into()),
        Term::from("norm_correct"),
        vec![],
        SubProofs(None),
    ));

    // Encode: rewrite left  .[x in _ = x] norm_correct;
    proof.push(ProofStep::Rewrite(
        true,
        Some("[x in _ = x]".into()),
        Term::from("norm_correct"),
        vec![],
        SubProofs(None),
    ));

    // Encode: reflexivity;
    proof.push(ProofStep::Reflexivity);

    proof
}
