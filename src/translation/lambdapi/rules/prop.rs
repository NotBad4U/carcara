//! Rules whose conclusion is a propositional tautology or a Boolean
//! rewrite, plus the Boolean cvc5 RARE rewrites and the Boolean half of
//! the *_simplify family. Mirrors `alethe-lp/prop.lp`.

use crate::translation::lambdapi::*;
use crate::ast::{Operator, Rc, Term as AletheTerm, match_term_err};
use std::ops::Deref;
use super::lia::{translate_arith_poly_norm,
    translate_evaluate_eq_arith, translate_evaluate_linear_arith};
use try_match::match_ok;
use crate::ast::{Constant, match_term};

/// Construct the proof term for the rule `false`
/// ```text
/// (step ti (cl (not false)) :rule false)
/// ```
/// we directly apply the lemma `neg_⊥`.
///
///
/// Translate the `true` rule (▷ ⊤). Without a dedicated case the rule name would resolve to
/// the Boolean constant `true` of Stdlib.Bool instead of a proof of `π ⊤`.
pub fn translate_true() -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᵢ₁";
        refine "⊤ᵢ";
    }))
}

pub fn translate_false() -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᵢ₁";
        refine "neg_⊥";
    }))
}

/// Rule `nary_elim`: relate an n-ary application to its binary unfolding.
///
/// ```text
/// (step t1 (cl (= (=> a b c) (=> a (=> b c)))) :rule nary_elim)
/// ```
///
/// The rule never appears in a solver's proof -- carcara's own polyeq
/// elaborator introduces it (`elaborate_assoc`, src/elaborator/polyeq/mod.rs)
/// whenever it has to normalise an n-ary term to the binary form the rest of
/// the proof uses. cvc5 emits n-ary `=>` and `=` freely, so any proof over a
/// three-or-more-argument connective reaches this.
///
/// It is discharged by reflexivity because the Lambdapi encoding has no n-ary
/// connective to begin with: `Operator::Implies` and `Operator::Equals` are
/// unfolded when the term is converted (`nary_implies` / `nary_equals` in
/// `syntax/term.rs`), so both sides of the equation are already the same term
/// and the rule is a no-op in the target. Nothing here has to reproduce
/// `expand_assoc` -- the conversion did it.
///
/// The shared-subterm aliases the backend emits (`symbol p_2 ≔ …`) are ordinary
/// definitions, not opaque, so Lambdapi's conversion δ-unfolds them; no
/// `simplify` is needed before `reflexivity`.
pub fn translate_nary_elim() -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᵢ₁";
        reflexivity;
    }))
}

/// Construct the proof term for the rule `implies`.
///
/// ```text
/// (assume h1 (=> a b))
/// (step t2 (cl (not a) b) :rule implies :premises (h1))
/// ```
///
/// We generate a proof term that use the lemma `implies` with the premise as parameter.
/// Following our example we should obtain: `apply (implies h1)`.
///
pub fn translate_implies(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "implies" (@unary_clause_to_prf(premise));
    }))
}

/// Construct the proof term for the rule `implies`.
///
/// ```text
/// (assume h1 (not (=> a b)))
/// (step t1 (cl a) :rule not_implies1 :premises (h1))
/// ```
///
/// We apply the direct corresponding lemma
///
pub fn translate_not_implies1(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "not_implies1" (@unary_clause_to_prf(premise));
    }))
}

/// Construct the proof term for the rule `implies`.
///
/// ```text
/// (assume h1 (not (=> a b)))
/// (step t1 (cl (not b)) :rule not_implies2 :premises (h1))
/// ```
///
/// We apply the direct corresponding lemma `not_implies2`
///
pub fn translate_not_implies2(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "not_implies2" (@unary_clause_to_prf(premise));
    }))
}

/// Rule 30: and
/// 𝑖. ⊳  𝜑0 ∧ ⋯ ∧ 𝜑n (...)
/// 𝑗. ⊳  𝜑n          (and 𝑖) k
///
///
/// ```text
/// refine ∧ₑₙ k (𝜑0 ⸬ ... ⸬ 𝜑𝑛 ⸬ □) ⊤ᵢ i
/// ```
pub fn translate_and(
    premise: &(String, &[Rc<AletheTerm>]),
    args: &[Rc<AletheTerm>],
) -> TradResult<Proof> {
    //let mut proof = vec![];

    // position of 𝜑𝑘 in sequent i. ▷ ¬(𝜑1 ∨ ⋯ ∨ 𝜑𝑛)
    let k = Term::Nat(
        args[0]
            .as_usize_err()
            .expect("missing index 𝑘 in :args")
            .try_into()
            .unwrap(),
    );

    // get 𝜑0 ∧ ⋯ ∧ 𝜑n from i
    let conj_list = Term::Alethe(LTerm::List(List(
        match_term_err!((and ...) = premise.1.first().unwrap())
            .unwrap()
            .iter()
            .rev()
            .map(std::convert::Into::into)
            .collect_vec(),
    )));

    let premise_id = premise.0.clone().into(); // i

    Ok(Proof(vec![ProofStep::Refine(
        terms!["∧ₑₙ".into(), ..vec![k, conj_list, intro_top(), premise_id],],
        SubProofs(None),
    )]))

    // Ok(Proof(vec![apply!("∨ᵢ₁".into()), projections]))
}

/// Rule `not_or`:
/// i. ▷ ¬(𝜑1 ∨ ⋯ ∨ 𝜑𝑛)
/// j. ▷ ¬𝜑𝑘
///
/// We solve this with this script:
/// ```text
/// refine not_or Stdlib.Nat._1 (𝜑1 ⸬ ... ⸬ 𝜑𝑛 ⸬ □)) ⊤ᵢ _;
/// simplify;
/// refine fold_⇒ _;
/// eval #repeat_or_id_r;
/// refine (π̇ₗ Goal);
/// ```
pub fn translate_not_or(
    premise: &(String, &[Rc<AletheTerm>]),
    args: &[Rc<AletheTerm>],
) -> TradResult<Proof> {
    let mut proof = vec![];

    // position of 𝜑𝑘 in sequent i. ▷ ¬(𝜑1 ∨ ⋯ ∨ 𝜑𝑛)
    let k = Term::Nat(
        args[0]
            .as_usize_err()
            .expect("missing index 𝑘 in :args")
            .try_into()
            .unwrap(),
    );

    // get 𝜑1 ∨ ⋯ ∨ 𝜑𝑛 from i
    let disj_list = List(
        match_term_err!((not (or ...)) = premise.1.first().unwrap())
            .unwrap()
            .iter()
            .rev()
            .map(std::convert::Into::into)
            .collect_vec(),
    );

    proof.push(ProofStep::Refine(
        terms![
            "not_or".into(),
            ..vec![
                k,
                Term::Alethe(LTerm::List(disj_list)),
                intro_top(),
                underscore!(),
            ]
        ],
        SubProofs(None),
    ));

    proof.push(ProofStep::Simplify(vec![]));

    proof.push(ProofStep::Refine(
        terms!["fold_⇒".into(), ..vec![underscore!()],],
        SubProofs(None),
    ));

    proof.push(ProofStep::Eval("#repeat_or_id_r".into()));

    proof.push(ProofStep::Refine(
        unary_clause_to_prf(&premise.0),
        SubProofs(None),
    ));

    Ok(Proof(proof))
}

/// Rule 32: or
/// transform a disjunction into a clause
/// 𝑖. ⊳ 𝜑1 ∨ ... ∨ 𝜑n    (...)
/// j. 𝜑1 , ... , 𝜑n.     (or i)
///
/// But in our case i will have the form `(𝜑1 ∨ ... ∨ 𝜑n) ⸬ □`
///
/// ```text
/// refine ∨ₑₙ (𝜑0 ⸬ ... ⸬ 𝜑𝑛 ⸬ □) _
/// simplify;
/// eval #repeat_or_id_r;
/// apply (π̇ₗ i)
/// ```
#[inline]
pub fn translate_or(premise: &(String, &[Rc<AletheTerm>])) -> TradResult<Proof> {
    let mut proof = vec![];

    // get 𝜑1 ∨ ⋯ ∨ 𝜑𝑛 from i
    let disj_list = Term::Alethe(LTerm::List(List(
        match_term_err!((or ...) = premise.1.first().unwrap())
            .unwrap()
            .iter()
            .rev()
            .map(std::convert::Into::into)
            .collect_vec(),
    )));

    let i = unary_clause_to_prf(premise.0.as_ref());

    proof.push(ProofStep::Refine(
        terms!["∨ₑₙ".into(), ..vec![disj_list, underscore!()]],
        SubProofs(None),
    ));

    proof.push(ProofStep::Simplify(vec![]));
    proof.push(ProofStep::Eval(Term::from("#repeat_or_id_r")));
    proof.push(ProofStep::Refine(i, SubProofs(None)));

    Ok(Proof(proof))
}

/// Rule `not_and`
/// i. ▷ ¬(𝜑1 ∧ … ∧ 𝜑𝑛)
/// j. ▷ ¬𝜑1, … , ¬𝜑𝑛
///
/// We want to produce the script:
///
///```text
/// refine not_and (𝜑1 ⸬ … ⸬ 𝜑𝑛 ⸬ □) (π̇ₗ i);
///```
pub fn translate_not_and(clause: &[Rc<AletheTerm>], premise: &str) -> TradResult<Proof> {
    let mut proof = vec![];

    // collect the list 𝜑1, ... 𝜑𝑛 from the clause ¬𝜑1, … , ¬𝜑𝑛
    let conj_list = List(
        clause
            .iter()
            .rev()
            .map(|t| {
                let phi = match_term_err!((not phi) = t).unwrap();
                phi.into()
            })
            .collect_vec(),
    );

    proof.push(ProofStep::Refine(
        terms![
            Term::from("not_and"),
            Term::Alethe(LTerm::List(conj_list)),
            unary_clause_to_prf(premise),
        ],
        SubProofs(None),
    ));

    Ok(Proof(proof))
}

/// Rule (𝜑1 ∧ ⋯ ∧ 𝜑𝑛), ¬𝜑1, … , ¬𝜑𝑛
/// we want to produce the script:
/// ```text
/// refine and_neg (𝜑1 ⸬ … ⸬ 𝜑𝑛 ⸬ □) _;
/// simplify;
/// eval #repeat_or_id_r;
/// reflexivity
/// ```
pub fn translate_and_neg(clause: &[Rc<AletheTerm>]) -> TradResult<Proof> {
    let mut proof = vec![];

    // values 𝜑1 ∧ ⋯ ∧ 𝜑𝑛 as List
    let conj_list = unwrap_match!(clause[0].deref(), AletheTerm::Op(Operator::And, e) => {
        List(e.iter().rev().map(std::convert::Into::into).collect_vec())
    });

    proof.push(ProofStep::Refine(
        terms![
            Term::TermId("and_neg".into()),
            ..vec![Term::Alethe(LTerm::List(conj_list)), Term::Underscore],
        ],
        SubProofs(None),
    ));
    proof.push(ProofStep::Simplify(vec![]));
    proof.push(ProofStep::Eval(Term::from("#repeat_or_id_r")));
    proof.push(ProofStep::Reflexivity);
    Ok(Proof(proof))
}

/// Rule `and_pos`: ¬(𝜑1 ∧ … ∧ 𝜑𝑛), 𝜑𝑘
/// we want to produce the script:
/// ```text
/// refine and_pos k (𝜑1 ⸬ … ⸬ 𝜑𝑛 ⸬ □) ⊤ᵢ;
/// ```
pub fn translate_and_pos(clause: &[Rc<AletheTerm>], args: &[Rc<AletheTerm>]) -> TradResult<Proof> {
    let mut proof = vec![];

    let conj_list = List(
        match_term_err!((not (and ...)) = &clause[0])
            .unwrap()
            .iter()
            .rev()
            .map(std::convert::Into::into)
            .collect_vec(),
    );

    let k = args[0].as_usize_err().unwrap();

    proof.push(ProofStep::Refine(
        terms![
            Term::from("and_pos"),
            ..vec![
                Term::Nat(k as u32),
                Term::Alethe(LTerm::List(conj_list)),
                intro_top(),
            ]
        ],
        SubProofs(None),
    ));

    Ok(Proof(proof))
}

/// Rule  `or_neg` (𝜑1 ∨ … ∨ 𝜑𝑛), ¬ 𝜑𝑘
/// we want to produce the script:
/// ```text
/// apply sym_clause;
/// refine or_neg k (𝜑1 ⸬ … ⸬ 𝜑𝑛 ⸬ □) _ ⊤ᵢ;
/// simplify;
/// eval #repeat_or_id_r;
/// reflexivity
/// ```
pub fn translate_or_neg(clause: &[Rc<AletheTerm>], args: &[Rc<AletheTerm>]) -> TradResult<Proof> {
    let mut proof = vec![];

    let disj_list = List(
        match_term_err!((or ...) = &clause[0])
            .unwrap()
            .iter()
            .rev()
            .map(std::convert::Into::into)
            .collect_vec(),
    );

    let k = args[0].as_usize_err().unwrap();

    proof.push(ProofStep::Apply(Term::from("sym_clause"), SubProofs(None)));

    proof.push(ProofStep::Refine(
        terms![
            Term::from("or_neg"),
            Term::Nat(k as u32),
            Term::Alethe(LTerm::List(disj_list)),
            Term::Underscore,
            intro_top(),
        ],
        SubProofs(None),
    ));

    proof.push(ProofStep::Simplify(vec![]));
    proof.push(ProofStep::Eval(Term::from("#repeat_or_id_r")));

    proof.push(ProofStep::Reflexivity);

    Ok(Proof(proof))
}

/// Translate the rule ite1
/// ```text
/// i. ▷ (ite 𝜑1 𝜑2 𝜑3)
/// j. ▷ 𝜑1, 𝜑3
/// ```
/// Since 𝜑2 does not appear in `j` clause we need to pass
///
pub fn translate_ite1(premise: &(String, &[Rc<AletheTerm>])) -> TradResult<Proof> {
    let term_ite = premise.1.first().expect("could not find ite term");
    if let [_c, t, _e, ..] =
        unwrap_match!(term_ite.deref(), AletheTerm::Op(Operator::Ite, cte) => cte.as_slice() )
    {
        Ok(proof!(
            apply!("ite1".into(), { underscore!(), t.into() , underscore!(), unary_clause_to_prf(&premise.0) } )
        ))
    } else {
        Err(TranslatorError::PremisesError)
    }
}

/// Translate the rule ite2:
/// ```text
/// i. ▷ (ite 𝜑1 𝜑2 𝜑3)
/// j. ▷ ¬ 𝜑1, 𝜑2
/// ```
///
pub fn translate_ite2(premise: &(String, &[Rc<AletheTerm>])) -> TradResult<Proof> {
    let term_ite = premise.1.first().expect("could not find ite term");
    if let [_c, _t, e, ..] =
        unwrap_match!(term_ite.deref(), AletheTerm::Op(Operator::Ite, cte) => cte.as_slice() )
    {
        Ok(proof!(
            apply!("ite2".into(), { underscore!(), underscore!(), e.into(), unary_clause_to_prf(&premise.0) } )
        ))
    } else {
        Err(TranslatorError::PremisesError)
    }
}

/// Translate the cvc5-specific `and_intro` rule: from the unit premises 𝜑1, …, 𝜑n, conclude
/// (and 𝜑1 … 𝜑n). Conjunction is right-nested in Lambdapi, so the proof term is
/// `clᵢ₁' (∧ᵢ (π̇ₗ p1) (∧ᵢ (π̇ₗ p2) (… (π̇ₗ pn))))`.
pub fn translate_and_intro(premises: &[(String, &[Rc<AletheTerm>])]) -> TradResult<Proof> {
    if premises.is_empty() || premises.iter().any(|(_, clause)| clause.len() != 1) {
        return Err(TranslatorError::PremisesError);
    }

    let conjunction = premises
        .iter()
        .rev()
        .map(|(id, _)| unary_clause_to_prf(id))
        .reduce(|acc, premise| terms![Term::from("∧ᵢ"), premise, acc])
        .unwrap();

    Ok(Proof(vec![ProofStep::Refine(
        terms![Term::from("clᵢ₁'"), conjunction],
        SubProofs(None),
    )]))
}

pub fn translate_rare_simp(
    clause: &[Rc<AletheTerm>],
    args: &[Rc<AletheTerm>],
    dag_terms: HashSet<String>,
) -> Proof {
    let (rare_rule, args) = args.split_first().unwrap();

    let rule: String =
        unwrap_match!(**rare_rule, crate::ast::Term::Const(Constant::String(ref s)) => s.clone());

    let mut simps: Vec<_> = if !dag_terms.is_empty() {
        dag_terms
            .into_iter()
            .map(|s| ProofStep::Simplify(vec![s]))
            .collect_vec()
    } else {
        vec![]
    };

    let mut rewrites = match rule.as_str() {
        "bool-eq-true" => translate_bool_eq_true(),
        "bool-eq-false" => translate_bool_eq_false(),
        "bool-and-true" => translate_bool_and_true(args),
        "bool-or-false" => translate_bool_or_false(args),
        "bool-or-flatten" => translate_bool_or_flatten(),
        "bool-and-flatten" => translate_bool_and_flatten(args),
        "bool-impl-elim" => translate_bool_impl_elim(),
        "bool-and-de-morgan" => translate_bool_and_de_morgan(),
        "bool-or-de-morgan" => translate_bool_or_de_morgan(),
        "bool-double-not-elim" => translate_bool_double_not_elim(),
        "bool-implies-or-distrib" => translate_bool_implies_or_distrib(args),
        "bool-impl-true1" => translate_bool_imp_true1(),
        "bool-impl-true2" => translate_bool_imp_true2(),
        "bool-impl-false1" => translate_bool_imp_false1(),
        "bool-impl-false2" => translate_bool_imp_false2(),
        "arith-poly-norm" => translate_arith_poly_norm(clause),
        "evaluate" => {
            let cl_first = clause.first().expect("evaluate can not be empty");
            match match_term!((= l r) = cl_first) {
                Some((l, r))
                    if (r.is_bool_false() || r.is_bool_true())
                        && (matches!(l.deref(), AletheTerm::Op(Operator::GreaterEq, _))
                            || matches!(l.deref(), AletheTerm::Op(Operator::LessEq, _))
                            || matches!(l.deref(), AletheTerm::Op(Operator::GreaterThan, _))
                            || matches!(l.deref(), AletheTerm::Op(Operator::LessThan, _))) =>
                {
                    translate_evaluate_linear_arith()
                }
                Some((_l, r)) if (r.is_bool_false() || r.is_bool_true()) => {
                    translate_evaluate_bool()
                }
                Some(_) => translate_evaluate_eq_arith(),
                None => panic!("not well formed evaluate, expected t1 = t2"),
            }
        }
        r => {
            let args = args.iter().map(std::convert::Into::into).collect_vec();
            vec![ProofStep::Apply(
                terms![Term::from(r), ..args],
                SubProofs(None),
            )]
        }
    };

    Proof(lambdapi! {
        apply "∨ᵢ₁";
        inject(simps);
        inject(rewrites);
    })
}

/// (define-rule bool-eq-true ((t Bool)) (= t true) t)
///
/// We translate it into:
/// ```text
/// simplify p_*;
/// rewrite ⊤=;
/// reflexivity;
/// ```
///
/// We simplify `p_*` all shared symbols otherwise the tactic `rewrite` does not work.
fn translate_bool_eq_true() -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(false, None, "=⊤".into(), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]
}

///(define-rule bool-eq-false ((t Bool)) (= t false) (not t))
///
/// We translate it into:
/// ```text
/// simplify p_*;
/// rewrite =⊥;
/// reflexivity;
/// ```
///
/// We simplify `p_*` all shared symbols otherwise the tactic `rewrite` does not work.
fn translate_bool_eq_false() -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(false, None, "=⊥".into(), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]
}

/// (define-rule bool-impl-false1 ((t Bool)) (=> t false) (not t))
fn translate_bool_imp_false1() -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(false, None, "⇒⊥".into(), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]
}

/// (define-rule bool-impl-false2 ((t Bool)) (=> false t) true)
fn translate_bool_imp_false2() -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(false, None, "⊥⇒".into(), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]
}

/// (define-rule bool-impl-true1 ((t Bool)) (=> t true) true)
fn translate_bool_imp_true1() -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(false, None, "⇒⊤".into(), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]
}

/// (define-rule bool-impl-true2 ((t Bool)) (=> true t) t)
fn translate_bool_imp_true2() -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(false, None, "⊤⇒".into(), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]
}

/// (define-rule bool-double-not-elim ((t Bool)) (not (not t)) t)
///
/// We translate it into:
/// ```text
/// simplify p_*;
/// rewrite ¬¬ₑ_eq;
/// reflexivity;
/// ```
///
/// We simplify `p_*` all shared symbols otherwise the tactic `rewrite` does not work.
fn translate_bool_double_not_elim() -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(false, None, "¬¬ₑ_eq".into(), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]
}

/// Provide a proof term for the `evaluate` rule that fold boolean constant.
/// For example:
/// ```text
/// (step ti (cl (= (not true) false)) :rule rare_rewrite :args ("evaluate"))
/// ```
fn translate_evaluate_bool() -> Vec<ProofStep> {
    // lambdapi! {
    //     simplify;
    //     apply "prop_ext";
    //     why3;
    // }
    vec![ProofStep::Admit]
}

// /// Translate (define-rule* bool-or-false ((xs Bool :list) (ys Bool :list)) (or xs false ys) (or xs ys))
fn translate_bool_or_false(args: &[Rc<AletheTerm>]) -> Vec<ProofStep> {
    let args = args
        .iter()
        .map(|term| unwrap_match!(**term, AletheTerm::Op(Operator::RareList, ref l) => l))
        .collect_vec();

    // If `xs` or `ys` rare-list are empty then we can not use the lemma bool-or-false because it expect 2 arguments.
    // we will use the `or_identity_l` or `or_identity_r` in that cases, otherwise we can use bool-and-true.

    if args[0].is_empty() {
        // argument `x` of and_identity_l lemma should be inferred by Lambdapi
        lambdapi! { rewrite "or_identity_l"; }
    } else if args[1].is_empty() {
        // argument `x` of and_identity_r lemma should be inferred by Lambdapi
        lambdapi! { rewrite "or_identity_r"; }
    } else {
        // let args: Vec<Term> = args
        //     .into_iter()
        //     .map(|terms| Term::from(AletheTerm::Op(Operator::RareList, terms.to_vec())))
        //     .collect_vec();
        // vec![ProofStep::Rewrite(None, Term::from("bool-or-false"), args)]
        lambdapi! { rewrite "or_identity_l"; }
    }
}

/// Translate the RARE rule:
/// `(define-rule* bool-and-true ((xs Bool :list) (ys Bool :list)) (and xs true ys) (and xs ys))`
fn translate_bool_and_true(args: &[Rc<AletheTerm>]) -> Vec<ProofStep> {
    let args = args
        .iter()
        .map(|term| unwrap_match!(**term, AletheTerm::Op(Operator::RareList, ref l) => l))
        .collect_vec();

    // If `xs` or `ys` rare-list are empty then we can not use the lemma bool-and-true because it expect 2 arguments.
    // we will use the `and_identity_l` or `and_identity_r` in that cases, otherwise we can use bool-and-true.

    if args[0].is_empty() {
        // argument `x` of and_identity_l lemma should be inferred by Lambdapi
        lambdapi! { rewrite "and_identity_l"; }
    } else if args[1].is_empty() {
        // argument `x` of and_identity_r lemma should be inferred by Lambdapi
        lambdapi! { rewrite "and_identity_r"; }
    } else {
        let args: Vec<Term> = args
            .into_iter()
            .map(|terms| Term::from(AletheTerm::Op(Operator::RareList, terms.clone())))
            .collect_vec();
        vec![
            ProofStep::Rewrite(
                false,
                None,
                Term::from("bool-and-true"),
                args,
                SubProofs(None),
            ),
            ProofStep::Reflexivity,
        ]
    }
}

fn translate_bool_impl_elim() -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(
            false,
            None,
            Term::from("bool-impl-elim"),
            vec![],
            SubProofs(None),
        ),
        ProofStep::Reflexivity,
    ]
}

// // (define-rule* bool-and-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list)) (and xs (and b ys) zs) (and xs b ys zs))
fn translate_bool_and_flatten(args: &[Rc<AletheTerm>]) -> Vec<ProofStep> {
    let xs = 0;
    let zs = 3;

    let args_len = args
        .iter()
        .map(|term| {
            match_ok!(**term, AletheTerm::Op(Operator::RareList, ref l) => l.len())
                .or_else(|| Some(1))
                .expect("can not convert rare-list")
        })
        .collect_vec();

    if args_len[xs] == 0 {
        lambdapi! {  rewrite "∧_assoc";  }
    } else if args_len[zs] == 0 {
        vec![]
    } else {
        let args: Vec<Term> = args.iter().map(std::convert::Into::into).collect_vec();
        vec![
            ProofStep::Rewrite(
                false,
                None,
                Term::from("bool-and-flatten"),
                args,
                SubProofs(None),
            ),
            ProofStep::Reflexivity,
        ]
    }
}

/// The Boolean half of the `*_simplify` family. `None` means the rule has no
/// script yet; the caller turns that into `UnsupportedRule` rather than
/// panicking, and the arithmetic and quantifier members of the family are
/// dispatched to their own modules instead of landing here.
pub fn translate_simplify_step(rule: &str) -> Option<Proof> {
    Some(match rule {
        "equiv_simplify" => translate_equiv_simplify(),
        "not_simplify" => translate_not_simplify(),
        "implies_simplify" => translate_implies_simplify(),
        "ite_simplify" => translate_ite_simplify(),
        "ac_simp" => translate_ac_simplify(),
        _ => return None,
    })
}

fn translate_equiv_simplify() -> Proof {
    Proof(lambdapi! {
        apply "∨ᵢ₁";
        simplify;
        eval "equiv_simplify";
    })
}

fn translate_not_simplify() -> Proof {
    Proof(lambdapi! {
        apply "∨ᵢ₁";
        simplify;
        eval "not_simplify";
    })
}

fn translate_implies_simplify() -> Proof {
    Proof(lambdapi! {
        apply "∨ᵢ₁";
        simplify;
        eval "implies_simplify";
    })
}

fn translate_ite_simplify() -> Proof {
    Proof(lambdapi! {
        apply "∨ᵢ₁";
        simplify;
        eval "ite_simplify";
    })
}

fn translate_ac_simplify() -> Proof {
    Proof(lambdapi! {
        apply "∨ᵢ₁";
        try [ rewrite "ac_simp_or"; ];
        try [ rewrite "ac_simp_and";  ];
        reflexivity;
    })
}

/// (define-rule* bool-and-de-morgan ((x Bool) (y Bool) (zs Bool :list))
///   (not (and x y zs))
///   (not (and y zs))
///   (or (not x) _))
///
/// eval #repeat (#rewrite morgan1);
///
/// We ignore arguments for this rule and take benefits of metatactics in Lambdapi.
fn translate_bool_and_de_morgan() -> Vec<ProofStep> {
    vec![
        ProofStep::Eval(Term::Terms(vec![
            "#repeat".into(),
            "#rewrite".into(),
            "morgan1".into(),
        ])),
        ProofStep::Reflexivity,
    ]
}

/// ```text
/// (define-rule* bool-or-de-morgan ((x Bool) (y Bool) (zs Bool :list))
///   (not (or x y zs))
///   (not (or y zs))
///   (and (not x) _))
/// ```
///
/// Translate into:
/// `eval #repeat (#rewrite morgan1);`
///
/// We ignore arguments for this rule and take benefits of metatactics in Lambdapi.
fn translate_bool_or_de_morgan() -> Vec<ProofStep> {
    vec![
        ProofStep::Eval(Term::Terms(vec![
            "#repeat".into(),
            "#rewrite".into(),
            "morgan2".into(),
        ])),
        ProofStep::Reflexivity,
    ]
}

/// ```text
/// (define-rule* bool-or-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list))
///     (or xs (or b ys) zs)
///     (or xs b ys zs))
/// ```
///
/// Translate into:
/// `eval #repeat (#rewrite morgan1);`
///
/// We ignore arguments for this rule and take benefits of metatactics in Lambdapi.
fn translate_bool_or_flatten() -> Vec<ProofStep> {
    vec![
        ProofStep::Eval(Term::Terms(vec![
            "#repeat".into(),
            "#rewrite".into(),
            "∨_assoc".into(),
        ])),
        ProofStep::Reflexivity,
    ]
}

/// ```text
///  (define-rule* bool-implies-or-distrib
///  ((y1 Bool) (y2 Bool) (ys Bool :list) (z Bool))
///      (=> (or y1 y2 ys) z)
///      (=> (or y2 ys) z)
///      (and (=> y1 z) _))
/// ```
fn translate_bool_implies_or_distrib(args: &[Rc<AletheTerm>]) -> Vec<ProofStep> {
    let mut proof = vec![];

    let y1: Term = args[0].clone().into();
    let y2: Term = args[1].clone().into();
    let ys = unwrap_match!(*args[2], AletheTerm::Op(Operator::RareList, ref l) => l);

    if ys.is_empty() {
        // argument `x` of and_identity_l lemma should be inferred by Lambdapi
        proof.push(ProofStep::Rewrite(
            false,
            None,
            "bool_implies_or_distrib".into(),
            vec![y1, y2],
            SubProofs(None),
        ));
    } else {
        let ys_term: Term = Term::from(AletheTerm::Op(Operator::RareList, ys.clone()));
        proof.push(ProofStep::Rewrite(
            false,
            None,
            "bool_implies_or_distrib_rec".into(),
            vec![y1, y2, ys_term],
            SubProofs(None),
        ));
    }

    proof.push(ProofStep::Reflexivity);

    proof
}

#[cfg(test)]
mod tests_tautolog {
    use super::*;
    use crate::terms;
    use crate::translation::lambdapi::test_macros::*;

    #[test]
    fn test_ite1() {
        let problem = "
            (declare-sort U 0)
            (declare-fun a() U)
            (declare-fun b() U)
            (declare-fun p(U) Bool)
        ";
        let proof = "
            (step t1 (cl (ite (p a) (= b (ite (p a) b a)) (= a (ite (p a) b a)))) :rule hole)
            (step t2 (cl (p a) (= a (ite (p a) b a))) :rule ite1 :premises (t1))
        ";
        let (_, proof, _, mut pool) = parse_test_instance(problem, proof).unwrap();

        assert_eq!(2, proof.commands.len());

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            &mut pool,
            &Config::default(),
            &mut Features::EMPTY,
            |id, t, ps| Command::Symbol(None, normalize_name(id), vec![], t, ps.map(Proof)),
        )
        .expect("translate forall_inst");

        assert_eq!(2, res.len());

        let t2 = res.last().unwrap().clone();

        let t = eq!(
            id!("b"),
            terms!(id!("ite"), terms!(id!("p"), id!("a")), id!("b"), id!("a"))
        );

        let cmd_expected = Command::Symbol(
            None,
            "t2".into(),
            vec![],
            cl!(
                terms![id!("p"), id!("a")],
                eq!(
                    id!("a"),
                    terms!(id!("ite"), terms!(id!("p"), id!("a")), id!("b"), id!("a"))
                )
            ),
            Some(proof!(
                apply!(id!("ite1"), { underscore!(),  t,  underscore!(), unary_clause_to_prf("t1") } )
            )),
        );

        assert_eq!(t2, cmd_expected);
    }

    #[test]
    fn test_ite2() {
        let problem = "
            (declare-sort U 0)
            (declare-fun a() U)
            (declare-fun b() U)
            (declare-fun p(U) Bool)
        ";
        let proof = "
            (step t1 (cl (ite (p a) (= b (ite (p a) b a)) (= a (ite (p a) b a)))) :rule hole)
            (step t2 (cl (not (p a)) (= b (ite (p a) b a))) :rule ite2 :premises (t1))
        ";
        let (_, proof, _, mut pool) = parse_test_instance(problem, proof).unwrap();

        assert_eq!(2, proof.commands.len());

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            &mut pool,
            &Config::default(),
            &mut Features::EMPTY,
            |id, t, ps| Command::Symbol(None, normalize_name(id), vec![], t, ps.map(Proof)),
        )
        .expect("translate forall_inst");

        assert_eq!(2, res.len());

        let t2 = res.last().unwrap().clone();

        let e = eq!(
            id!("a"),
            terms!(id!("ite"), terms!(id!("p"), id!("a")), id!("b"), id!("a"))
        );

        let cmd_expected = Command::Symbol(
            None,
            "t2".into(),
            vec![],
            cl!(
                not!(Term::Terms(vec![id!("p"), id!("a")])),
                eq!(
                    id!("b"),
                    terms!(id!("ite"), terms!(id!("p"), id!("a")), id!("b"), id!("a"))
                )
            ),
            Some(proof!(
                apply!(id!("ite2"), { underscore!(),  underscore!(),  e, unary_clause_to_prf("t1") } )
            )),
        );

        assert_eq!(t2, cmd_expected);
    }
}
