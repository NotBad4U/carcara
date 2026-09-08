//! Quantifier and binder rules. Mirrors `alethe-lp/quant.lp`.

use crate::translation::lambdapi::*;
use crate::ast::{Binder, Rc, Term as AletheTerm, match_term};
use std::ops::Deref;
use try_match::match_ok;

/// Construct the proof term to validate `forall_inst` rule.
/// Considering the example below:
/// ```text
/// (step tᵢ (cl (or (not (forall ((x S) (y T)) (P y x )))
/// (P b (f a))
/// :rule forall_inst :args ((f a) b)
/// ```
///
/// We will translate `forall_inst` changing the or (not a) b into an implication.
/// Passing the left handside into the hypothesis and then applying
/// n-|args| times forall eliminator.
///
/// NOTE: The convertion of arguments do not use the context for sharing the symbol for now.
///
/// Thus, the example is translated into the proof script:
/// ```text
/// have tᵢ: (((¬ (`∀ ((x: τ S) (y: τ T)) (P y x ))) ∨ (P b (f a))) ⸬ □) {
///     apply ∨ᵢ₁;
///     apply imply_to_or;  
///     assume H;
///     apply H b (f a)
/// }
/// ```
pub fn translate_forall_inst(args: &[Rc<AletheTerm>]) -> TradResult<Proof> {
    let mut hyp = vec![Term::from("H")];

    hyp.append(&mut args.iter().map(Term::from).collect_vec());

    let forall_elims = Term::Terms(hyp);

    Ok(Proof(lambdapi! {
        apply "∨ᵢ₁";
        apply "imply_to_or";
        assume [H]; //FIXME: use hyp instead
        refine (forall_elims);
    }))
}

/// Translate the `sko_forall` rule: replace a universally quantified formula by
/// its Skolemisation.
///
/// ```text
/// (step t (cl (= (forall ((x S) (y T)) F) F')) :rule sko_forall)
/// ```
///
/// `quant.lp`'s `sko_forall` peels exactly one binder:
///
/// ```text
/// (Π x, π (x = `ϵ y, ¬ (p y)) → π (p x = q)) → π ((`∀ x, p x) = q)
/// ```
///
/// so it has to be applied once per bound variable. Applying it only once left
/// `∀ y, …` on the left while `F'` had every variable Skolemised, and the
/// closing `reflexivity` failed with "is not unifiable with". The witnesses line
/// up because each application skolemises the body the previous one produced,
/// which is the nesting Alethe specifies for a quantifier prefix.
///
/// Binder names are numbered rather than taken from the Alethe step: the
/// hypothesis of one round is rewritten away before the next `apply`, so the
/// names are local and never collide with the problem's own symbols.
pub fn translate_sko_forall(clause: &[Rc<AletheTerm>]) -> TradResult<Proof> {
    let arity = sko_forall_arity(clause);

    let mut proof = vec![ProofStep::Apply(Term::from("∨ᵢ₁"), SubProofs(None))];
    for i in 0..arity {
        let h = format!("H{i}");
        proof.push(ProofStep::Apply(
            Term::from("sko_forall"),
            SubProofs(None),
        ));
        proof.push(ProofStep::Assume(vec![format!("x{i}"), h.clone()]));
        proof.push(ProofStep::Rewrite(
            false,
            None,
            Term::from(h),
            vec![],
            SubProofs(None),
        ));
    }
    proof.push(ProofStep::Reflexivity);

    Ok(Proof(proof))
}

/// How many variables the `sko_forall` step's quantifier binds. Falls back to 1,
/// the single-binder shape, when the conclusion is not the expected
/// `(= (forall …) _)`.
fn sko_forall_arity(clause: &[Rc<AletheTerm>]) -> usize {
    clause
        .first()
        .and_then(|c| match_term!((= f _) = c))
        .and_then(|(f, _)| {
            match_ok!(f.deref(), AletheTerm::Binder(Binder::Forall, bs, _) => bs.len())
        })
        .filter(|n| *n > 0)
        .unwrap_or(1)
}
