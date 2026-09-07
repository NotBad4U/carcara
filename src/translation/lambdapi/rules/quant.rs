//! Quantifier and binder rules. Mirrors `lambdapi-stdlib/quant.lp`.

use crate::translation::lambdapi::*;
use crate::ast::{Rc, Term as AletheTerm};

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
/// have tᵢ: (((¬ (`∀ ((x: τ S) (y: τ T)) (P y x ))) ∨ (P b (f a))) ⟇ ▩) {
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

pub fn translate_sko_forall() -> TradResult<Proof> {
    // Ok(Proof(lambdapi! {
    //     apply "∨ᵢ₁";
    //     apply "sko_forall";
    //     assume [x H];
    //     rewrite "H";
    //     reflexivity;
    // }))
    Ok(Proof(admit()))
}
