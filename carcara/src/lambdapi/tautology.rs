use super::*;
use crate::ast::{Operator, Rc, Term as AletheTerm};

pub fn translate_trans(premises: &[(String, &[Rc<AletheTerm>])]) -> TradResult<Proof> {
    fn make_transitivity_list(premises: &[(String, &[Rc<AletheTerm>])]) -> Term {
        if premises.len() == 1 {
            unary_clause_to_prf(premises[0].0.as_str())
        } else {
            make_term!{ "⟺ᶜ_trans" ((@unary_clause_to_prf(premises[0].0.as_str())) (@make_transitivity_list(&premises[1..]))) }
        }
    }

    Ok(Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        apply @make_transitivity_list(premises);
    }))
}

pub fn translate_implies(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "implies" (@unary_clause_to_prf(premise));
    }))
}

pub fn translate_not_implies1(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "not_implies1" (@unary_clause_to_prf(premise));
    }))
}

pub fn translate_not_implies2(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "not_implies2" (@unary_clause_to_prf(premise));
    }))
}

pub fn translate_not_and(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "not_and" (@unary_clause_to_prf(premise));
        reflexivity;
    }))
}

pub fn translate_refl() -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        apply "⟺ᶜ_refl";
    }))
}

pub fn translate_sym(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        apply "⟺ᶜ_sym" (@unary_clause_to_prf(premise));
    }))
}

pub fn translate_and(premise: &(String, &[Rc<AletheTerm>])) -> TradResult<Proof> {
    let mut conjonctions_vec = unwrap_match!(premise.1.first().unwrap().deref(), AletheTerm::Op(Operator::And, args) => args)
        .into_iter()
        .map(From::from)
        .collect_vec();

    conjonctions_vec.push(Term::Alethe(LTerm::True));

    let conjonctions = Term::Alethe(LTerm::NAnd(conjonctions_vec));

    let t_i = premise.0.clone();

    Ok(Proof(lambdapi! {
        apply "and" (@conjonctions)
        {  reflexivity; }
        { apply t_i; };
    }))
}

pub fn translate_not_or(premise: &(String, &[Rc<AletheTerm>])) -> TradResult<Proof> {
    let apply_identity = Proof(vec![ProofStep::Apply(
        Term::TermId("identity_⊥".into()),
        vec![Term::from(premise.0.clone())],
        SubProofs(None),
    )]);
    let reflexivity = Proof(vec![ProofStep::Reflexivity]);

    let disjunctions = unwrap_match!(premise.1.first().unwrap().deref(), AletheTerm::Op(Operator::Not, args) => args)
        .into_iter()
        .map(From::from)
        .collect_vec();

    Ok(Proof(vec![ProofStep::Apply(
        Term::TermId("not_or".into()),
        vec![Term::Terms(disjunctions)],
        SubProofs(Some(vec![apply_identity, reflexivity])),
    )]))
}

#[inline]
pub fn translate_or(premise_id: &str) -> TradResult<Proof> {
    Ok(Proof(vec![ProofStep::Apply(
        Term::TermId("π̇ₗ".into()),
        vec![Term::TermId(premise_id.into())],
        SubProofs(None),
    )]))
}

#[inline]
pub fn translate_auto_rewrite(rule: &str) -> TradResult<Proof> {
    Ok(Proof(vec![
        ProofStep::Apply(Term::TermId(rule.into()), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]))
}

pub fn translate_cong(
    clause: &[Rc<AletheTerm>],
    premises: &[(String, &[Rc<AletheTerm>])],
) -> TradResult<Proof> {
    let (operator, arity) = unwrap_match!(clause[0].deref(), AletheTerm::Op(Operator::Equals, ts) => {
        match (&*ts[0], &*ts[1]) {
            (AletheTerm::App(f, args) , AletheTerm::App(g, _)) if f == g => (Term::from((*f).clone()),  args.len()),
            (AletheTerm::Op(f, args) , AletheTerm::Op(g, _)) if f == g => (Term::from(*f), args.len()),
            _ => unreachable!()
        }
    });

    Ok(Proof(vec![ProofStep::Admit]))
}

pub fn translate_simple_tautology(
    rule: &str,
    premises: &[(String, &[Rc<AletheTerm>])],
) -> TradResult<Proof> {
    Ok(Proof(vec![ProofStep::Apply(
        translate_rule_name(rule),
        premises
            .into_iter()
            .map(|(name, _)| Term::TermId(name.to_string()))
            .collect_vec(),
        SubProofs(None),
    )]))
}

/// Create a proof step for tautology step.
/// TODO: This feature need the RARE rewriting system to be implemented.
pub fn translate_simplification(
    _ctx: &Context,
    id: &str,
    clause: &[Rc<AletheTerm>],
    _rule: &str,
) -> TradResult<ProofStep> {
    let terms = clause.into_iter().map(|a| Term::from(a)).collect();

    Ok(ProofStep::Have(
        id.to_string(),
        proof(Term::Alethe(LTerm::Clauses(terms))),
        vec![ProofStep::Admit],
    ))
}

pub fn translate_forall_inst(args: &[ProofArg]) -> TradResult<Proof> {
    let hyp = Term::from("H");

    // The term Term::from("H") is related to assume [H];
    let init_forall_elim = Term::Terms(vec![
        Term::from("∀ᶜₑ"),
        unwrap_match!(args.first(), Some(ProofArg::Assign(_, t)) => t.into()),
        hyp,
    ]);

    let forall_elims = args
        .into_iter()
        .skip(1)
        .fold(init_forall_elim, |acc, arg| {
            Term::Terms(vec![
                Term::from("∀ᶜₑ"),
                unwrap_match!(arg, ProofArg::Assign(_, t) => t.into()),
                acc,
            ])
        });

    Ok(Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        apply "imply_to_or";
        apply "⟹ᶜᵢ";
        assume [H]; //FIXME: use hyp instead
        apply "∨ᶜᵢ₁" (@forall_elims);
    }))
}
