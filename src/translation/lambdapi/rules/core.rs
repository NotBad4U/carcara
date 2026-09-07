//! Rules of the Alethe calculus itself: equality and congruence, and the
//! clause-level rules. Mirrors `alethe-lp/core.lp`.

use crate::translation::lambdapi::rules::{get_premises_clause, unary_clause_to_prf};
use crate::translation::lambdapi::*;
use crate::ast::{Operator, Rc, Term as AletheTerm};
use std::ops::Deref;

/// Generate the proof term for the rule `trans` e.g.
/// ```text
///  (assume h1 (= a b))
///  (assume h2 (= b c))
///  (assume h3 (= c d))
/// (step ti (cl (= a d)) :rule trans :premises (h1 h2 h3))
/// ```
///
/// sConstruct a proof term that compose n-1 application of the lemma `trans`
/// where n is the cardinality of the premises set. Given our example, we will
/// translate this proof step `ti` into `apply trans (h1 trans (h2 h3))`.
///
pub fn translate_trans(premises: &mut Vec<(String, &[Rc<AletheTerm>])>) -> TradResult<Proof> {
    // The elaborator can sometime optimise useless transitivity leting only a single hypothesis
    if premises.len() == 1 {
        let (premise_name, _) = premises.first().unwrap();
        return Ok(Proof(lambdapi! {
            apply @(premise_name);
        }));
    }

    let tn_t_succ_n = premises.drain(premises.len() - 2..).take(2).collect_vec();

    let first_trans = Term::Terms(vec![
        Term::from("trans"),
        Term::from(tn_t_succ_n[0].0.as_str()),
        Term::from(tn_t_succ_n[1].0.as_str()),
    ]);

    let proofterm = premises.iter_mut().rev().fold(first_trans, |mut acc, p| {
        acc = Term::Terms(vec![Term::from("trans"), Term::from(p.0.as_str()), acc]);
        acc
    });

    let proofstep = vec![ProofStep::Apply(proofterm, SubProofs(None))];

    Ok(Proof(proofstep))
}

pub fn translate_refl() -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᵢ₁";
        reflexivity;
    }))
}

pub fn translate_sym(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᵢ₁";
        symmetry;
        apply @unary_clause_to_prf(premise);
    }))
}

/// Rule 12: `not_symm`
/// i. `¬(𝑡1 ≈ 𝑡2)`
/// j. `¬(𝑡2 ≈ 𝑡1)`
///     
///
/// /// is translated into the script:
/// ```text
/// refine not_symm [[i]];
/// ```
pub fn translate_not_symm(premise: &str) -> TradResult<Proof> {
    let mut proof = vec![];
    proof.push(ProofStep::Apply(Term::from("∨ᵢ₁"), SubProofs(None)));
    proof.push(ProofStep::Refine(
        terms![Term::from("not_symm"), ..vec![unary_clause_to_prf(premise)],],
        SubProofs(None),
    ));
    Ok(Proof(proof))
}

fn propositional_or_cong(premises: &[(String, &[Rc<AletheTerm>])]) -> TradResult<Proof> {
    fn cong_tree(premises: &[(String, &[Rc<AletheTerm>])]) -> Proof {
        match premises.split_first() {
            Some((p, rest)) if !rest.is_empty() => {
                let p_proof = Proof(vec![ProofStep::Apply(
                    Term::from(p.0.as_str()),
                    SubProofs(None),
                )]);
                Proof(vec![ProofStep::Apply(
                    Term::from("cong_or"),
                    SubProofs(Some(vec![p_proof, cong_tree(rest)])),
                )])
            }
            Some((p, [])) => Proof(vec![ProofStep::Apply(
                Term::from(p.0.as_str()),
                SubProofs(None),
            )]),
            _ => unreachable!("we should stop when rest is empty"),
        }
    }

    Ok(cong_tree(premises))
}

fn propositional_and_cong(premises: &[(String, &[Rc<AletheTerm>])]) -> TradResult<Proof> {
    fn cong_tree(premises: &[(String, &[Rc<AletheTerm>])]) -> Proof {
        match premises.split_first() {
            Some((p, rest)) if !rest.is_empty() => {
                let p_proof = Proof(vec![ProofStep::Apply(
                    Term::from(p.0.as_str()),
                    SubProofs(None),
                )]);
                Proof(vec![ProofStep::Apply(
                    Term::from("cong_and"),
                    SubProofs(Some(vec![p_proof, cong_tree(rest)])),
                )])
            }
            Some((p, [])) => Proof(vec![ProofStep::Apply(
                Term::from(p.0.as_str()),
                SubProofs(None),
            )]),
            _ => unreachable!("we should stop when rest is empty"),
        }
    }

    Ok(cong_tree(premises))
}

fn ite_cong(premises: &[(String, &[Rc<AletheTerm>])]) -> TradResult<Proof> {
    let premises = premises
        .iter()
        .map(|p| unary_clause_to_prf(p.0.as_str()))
        .collect_vec();

    Ok(proof!(ProofStep::Apply(
        terms!["ite_cong".into(), ..premises,],
        SubProofs(None)
    )))
}

fn propositional_cong(
    symbol: Term,
    arity: usize,
    premises: &[(String, &[Rc<AletheTerm>])],
) -> TradResult<Proof> {
    if arity == 1 {
        let premise = premises
            .first()
            .map(|p| unary_clause_to_prf(p.0.as_str()))
            .expect("Missing premise");

        Ok(Proof(lambdapi! {
            apply "∨ᵢ₁";
            inject(vec![ProofStep::Apply(terms![Term::from("feq"), symbol, premise], SubProofs(None))]);
        }))
    } else {
        match symbol {
            Term::TermId(s) if s == "(∨)" => propositional_or_cong(premises),
            Term::TermId(s) if s == "(∧)" => propositional_and_cong(premises),
            _ => {
                // Case `iff`, `=>` ...
                let premises_rev = premises.iter().rev().collect_vec();
                let (left, right) = premises_rev.split_at(2);

                let feq_first = Term::Terms(vec![
                    Term::from("feq2"),
                    symbol.clone(),
                    unary_clause_to_prf(left[1].0.as_str()),
                    unary_clause_to_prf(left[0].0.as_str()),
                ]);

                let feq = right.iter().fold(feq_first, |acc, (hyp, _)| {
                    Term::Terms(vec![
                        Term::from("feq2"),
                        symbol.clone(),
                        unary_clause_to_prf(hyp),
                        acc,
                    ])
                });

                Ok(Proof(lambdapi! {
                    apply "∨ᵢ₁";
                    inject(vec![ProofStep::Apply(feq, SubProofs(None))]);
                }))
            }
        }
    }
}

fn application_cong(
    symbol: Term,
    arity: usize,
    premises: &[(String, &[Rc<AletheTerm>])],
) -> TradResult<Proof> {
    let feq_name = if arity > 1 {
        Term::from(format!("feq{}", arity))
    } else {
        Term::from("feq")
    };

    let mut args = vec![symbol];

    let mut hyps = premises
        .iter()
        .map(|p| unary_clause_to_prf(p.0.as_str()))
        .collect_vec();

    args.append(&mut hyps);

    let feq = ProofStep::Apply(terms![feq_name, ..args], SubProofs(None));

    Ok(Proof(lambdapi! {
        apply "∨ᵢ₁";
        inject(vec![feq]);
    }))
}

/// Construct the proof term for the rule `cong`
/// The cong rule is applied on any n-ary function symbol `f` of appropriate sort.
/// Therefore, first we collect information about the sort of `f`, its arguments and its arity by looking at the clause and number of premises.
/// The application of cong on `f: A₁ ... Aₙ → Set` are translated with the lemma feqₙ where `n` is the arity of `f`.
/// The application of cong on `or` and `and` operator are translated by composing the lemma `cong_or` (`cong_and` respectively).
/// For the operators `(imp a b)` and `(not a)` we apply the lemma feq₂ and (`feq` respectively) since we can quantify over propositions with `ο`.
pub fn translate_cong(
    clause: &[Rc<AletheTerm>],
    premises: &[(String, &[Rc<AletheTerm>])],
) -> TradResult<Proof> {
    let (operator, symbol, f_args, g_args) = unwrap_match!(clause[0].deref(), AletheTerm::Op(Operator::Equals, ts) => {
        match (&*ts[0], &*ts[1]) {
            (AletheTerm::App(f, f_args) , AletheTerm::App(g, g_args)) if f == g => (None, Term::from((*f).clone()), f_args, g_args),
            (AletheTerm::Op(f, f_args) , AletheTerm::Op(g, g_args)) if f == g => (Some(f), Term::from(*f), f_args, g_args),
            _ => unreachable!()
        }
    });
    let arity = f_args.len();

    // The Alethe `cong` rule does not require a premise for pairs of arguments that are
    // syntactically equal, and cvc5 omits them. The Lambdapi lemmas expect one proof per
    // argument, so we justify those pairs with local reflexivity hypotheses, pairing the
    // premises with the arguments exactly like the checker does.
    let mut refl_steps = Vec::new();
    let mut full_premises: Vec<(String, &[Rc<AletheTerm>])> = Vec::with_capacity(arity);
    let mut remaining = premises.iter().peekable();
    for (k, (f_arg, g_arg)) in f_args.iter().zip(g_args).enumerate() {
        let justified = remaining.peek().is_some_and(|(_, premise)| {
            premise.first().is_some_and(|t| {
                matches!(t.deref(), AletheTerm::Op(Operator::Equals, ts)
                    if (&ts[0] == f_arg && &ts[1] == g_arg) || (&ts[0] == g_arg && &ts[1] == f_arg))
            })
        });
        if justified || f_arg != g_arg {
            full_premises.push(remaining.next().expect("cong: missing premise").clone());
        } else {
            let name = format!("cong_refl_{}", k);
            let goal = Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(vec![
                Term::Alethe(LTerm::Eq(
                    Box::new(Term::from(f_arg)),
                    Box::new(Term::from(g_arg)),
                )),
            ])))));
            refl_steps.push(ProofStep::Have(
                name.clone(),
                goal,
                lambdapi! {
                    apply "clᵢ₁'";
                    reflexivity;
                },
            ));
            full_premises.push((name, std::slice::from_ref(f_arg)));
        }
    }

    let Proof(cong_steps) = if matches!(operator, Some(Operator::Ite)) {
        ite_cong(&full_premises)?
    } else if operator.is_some() {
        propositional_cong(symbol, arity, &full_premises)?
    } else {
        application_cong(symbol, arity, &full_premises)?
    };

    refl_steps.extend(cong_steps);
    Ok(Proof(refl_steps))
}

/// Rule 9 contraction:
///```text
/// 𝑖. ⊳ 𝑙1, ... , 𝑙n    (...)
/// 𝑗. ⊳  𝑙𝑘1, ... , 𝑙kn (contraction i)
///```
///
/// Removes duplicated literal and does not reorder the literals.
///
/// ```text
///   assume we have i: π̇ (𝑙𝑘1, ... , 𝑙kn)
///
///   have H : π (disj 𝑙1, ... , 𝑙n = disj 𝑙𝑘1, ... , 𝑙kn) {
///     set r ≔ reify_cl 𝑙1, ... , 𝑙n;
///     change π (den (r ₂) (r ₁) = disj 𝑙𝑘1, ... , 𝑙kn);
///     rewrite left contraction_correct;
///     reflexivity
///   };
///   refine subst_equiv_clause (𝑙1, ... , 𝑙n) (𝑙𝑘1, ... , 𝑙kn)  H i
/// end;
/// ```
pub fn translate_contraction(
    clause: &[Rc<AletheTerm>],
    premise: &(String, &[Rc<AletheTerm>]),
) -> TradResult<Proof> {
    let mut proof = vec![];

    let i = premise.0.clone().into();

    let i_cl = Term::Alethe(LTerm::Clauses(
        premise.1.iter().map(Into::into).collect_vec(),
    ));

    let j_cl = Term::Alethe(LTerm::Clauses(clause.iter().map(Into::into).collect_vec()));

    // reify_i represents reify_cl 𝑙1, ... , 𝑙n
    let reify_i = Term::Terms(vec!["reify_cl".into(), i_cl.clone()]);

    let alias_reify_i = "ir";

    proof.push(ProofStep::Set(alias_reify_i.into(), reify_i.clone()));

    // conv_i represents disj 𝑙1, ... , 𝑙n
    let conv_i = Term::Terms(vec!["disj".into(), i_cl.clone()]);

    // conv_j represents disj 𝑙𝑘1, ... , 𝑙kn
    let conv_j = Term::Terms(vec!["disj".into(), j_cl.clone()]);

    // π (disj 𝑙1, ... , 𝑙n = disj 𝑙𝑘1, ... , 𝑙kn)
    let goal_contra = Term::Alethe(LTerm::ClassicProof(Box::new(Term::Alethe(LTerm::Eq(
        Box::new(conv_i.clone()),
        Box::new(conv_j.clone()),
    )))));

    let have_id = "H";

    // π (den (r ₂) (r ₁) = disj 𝑙1, ... , 𝑙n);
    let change = ProofStep::Change(Term::Alethe(LTerm::ClassicProof(Box::new(Term::Alethe(
        LTerm::Eq(
            Box::new(Term::Terms(vec![
                "den".into(),
                Term::Terms(vec![alias_reify_i.into(), "₂".into()]),
                Term::Terms(vec![alias_reify_i.into(), "₁".into()]),
            ])),
            Box::new(conv_j.clone()),
        ),
    )))));

    //   have eq : π (disj 𝑙1, ... , 𝑙n = disj 𝑙1, ... , 𝑙n) {
    //     set r ≔ ...;
    //     change ...;
    //   };
    proof.push(ProofStep::Have(
        have_id.to_owned(),
        goal_contra,
        vec![
            change,
            ProofStep::Rewrite(
                true,
                None,
                "contraction_correct".into(),
                vec![],
                SubProofs(None),
            ),
            ProofStep::Reflexivity,
        ],
    ));

    proof.push(ProofStep::Refine(
        terms!["subst_equiv_clause".into(), i_cl, j_cl, have_id.into(), i],
        SubProofs(None),
    ));

    Ok(Proof(proof))
}

#[cfg(test)]
mod tests_tautolog {
    use super::*;
    use crate::terms;
    use crate::translation::lambdapi::test_macros::*;

    #[test]
    fn test_transitivity_translation() {
        let problem = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
            (declare-fun c () T)
            (declare-fun d () T)
            (declare-fun e () T)
        ";
        let proof = "
            (assume h1 (= a b))
            (assume h2 (= b c))
            (assume h3 (= c d))
            (step t1 (cl (= a d)) :rule trans :premises (h1 h2 h3))
        ";
        let (_, proof, _, mut pool) = parse_test_instance(problem, proof).unwrap();

        assert_eq!(4, proof.commands.len());

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            &mut pool,
            &Config::default(),
            &mut Features::EMPTY,
            |id, t, ps| Command::Symbol(None, normalize_name(id), vec![], t, ps.map(Proof)),
        )
        .expect("translate trans");

        assert_eq!(4, res.len());

        let t1 = res.last().unwrap().clone();

        assert_eq!(
            t1,
            Command::Symbol(
                None,
                "t1".into(),
                vec![],
                cl!(eq!(bid!("a"), bid!("d"))),
                Some(proof!(apply!(terms!(
                    id!("trans"),
                    id!("h1"),
                    terms!(id!("trans"), id!("h2"), id!("h3"))
                ))))
            )
        );
    }

    #[test]
    fn test_cong_or_translation() {
        let problem = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
            (declare-fun d () Bool)
            (declare-fun e () Bool)
            (declare-fun f () Bool)
            (declare-fun g () Bool)
            (declare-fun h () Bool)
        ";
        let proof = "
            (assume h1 (= a e))
            (assume h2 (= b f))
            (assume h3 (= c g))
            (assume h4 (= d h))
            (step t3 (cl (= (or a b c d) (or e f g h))) :rule cong :premises (h1 h2 h3 h4))
        ";
        let (_, proof, _, mut pool) = parse_test_instance(problem, proof).unwrap();

        assert_eq!(5, proof.commands.len());

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            &mut pool,
            &Config::default(),
            &mut Features::EMPTY,
            |id, t, ps| Command::Symbol(None, normalize_name(id), vec![], t, ps.map(Proof)),
        )
        .expect("translate cong");

        assert_eq!(5, res.len());

        let t3 = res.last().unwrap().clone();

        let cmd = Command::Symbol(
            None,
            "t3".into(),
            vec![],
            cl!(eq!(
                or![id!("a"), id!("b"), id!("c"), id!("d"),],
                or![id!("e"), id!("f"), id!("g"), id!("h"),]
            )),
            Some(proof!(apply!(
                cong_or,
                {},
                [
                    apply!(h1),
                    apply!(
                        cong_or,
                        {},
                        [apply!(h2), apply!(cong_or, {}, [apply!(h3), apply!(h4)]),]
                    )
                ]
            ))),
        );

        assert_eq!(t3, cmd);
    }

    #[test]
    fn test_cong_and_translation() {
        let problem = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
            (declare-fun d () Bool)
            (declare-fun e () Bool)
            (declare-fun f () Bool)
            (declare-fun g () Bool)
            (declare-fun h () Bool)
        ";
        let proof = "
            (assume h1 (= a e))
            (assume h2 (= b f))
            (assume h3 (= c g))
            (assume h4 (= d h))
            (step t3 (cl (= (and a b c d) (and e f g h))) :rule cong :premises (h1 h2 h3 h4))
        ";
        let (_, proof, _, mut pool) = parse_test_instance(problem, proof).unwrap();

        assert_eq!(5, proof.commands.len());

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            &mut pool,
            &Config::default(),
            &mut Features::EMPTY,
            |id, t, ps| Command::Symbol(None, normalize_name(id), vec![], t, ps.map(Proof)),
        )
        .expect("translate cong");

        assert_eq!(5, res.len());

        let t3 = res.last().unwrap().clone();

        let cmd = Command::Symbol(
            None,
            "t3".into(),
            vec![],
            cl!(eq!(
                and![id!("a"), id!("b"), id!("c"), id!("d"),],
                and![id!("e"), id!("f"), id!("g"), id!("h"),]
            )),
            Some(proof!(apply!(
                cong_and,
                {},
                [
                    apply!(h1),
                    apply!(
                        cong_and,
                        {},
                        [apply!(h2), apply!(cong_and, {}, [apply!(h3), apply!(h4)]),]
                    )
                ]
            ))),
        );

        assert_eq!(t3, cmd);
    }

    #[test]
    fn test_cong_not_translation() {
        let problem = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
        ";
        let proof = "
            (assume h1 (= a b))
            (step t3 (cl (= (not a) (not b))) :rule cong :premises (h1))
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
        .expect("translate cong");

        assert_eq!(2, res.len());

        let t3 = res.last().unwrap().clone();

        let cmd = Command::Symbol(
            None,
            "t3".into(),
            vec![],
            cl!(eq!(not!(id!("a")), not!(id!("b")))),
            Some(proof!(
                apply!(id!("∨ᵢ₁")),
                apply!(
                    id!("feq"),
                    { id!("(¬)"), unary_clause_to_prf("h1") }
                )
            )),
        );

        assert_eq!(t3, cmd);
    }

    #[test]
    fn test_cong_imp_translation() {
        let problem = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
            (declare-fun d () Bool)
        ";
        let proof = "
            (assume h1 (= a c))
            (assume h2 (= b d))
            (step t3 (cl (= (=> a b) (=> c d))) :rule cong :premises (h1 h2))
        ";
        let (_, proof, _, mut pool) = parse_test_instance(problem, proof).unwrap();

        assert_eq!(3, proof.commands.len());

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            &mut pool,
            &Config::default(),
            &mut Features::EMPTY,
            |id, t, ps| Command::Symbol(None, normalize_name(id), vec![], t, ps.map(Proof)),
        )
        .expect("translate cong");

        assert_eq!(3, res.len());

        let t3 = res.last().unwrap().clone();

        let cmd = Command::Symbol(
            None,
            "t3".into(),
            vec![],
            cl!(eq!(imp!(id!("a"), id!("b")), imp!(id!("c"), id!("d")))),
            Some(proof!(
                apply!(id!("∨ᵢ₁")),
                apply!(terms![
                    id!("feq2"),
                    id!("(⇒)"),
                    unary_clause_to_prf("h1"),
                    unary_clause_to_prf("h2")
                ])
            )),
        );

        assert_eq!(t3, cmd);
    }
}

/* The resolution family: the clause-level rules of the Alethe calculus. */

fn get_pivots_from_args(args: &[Rc<AletheTerm>]) -> Vec<(Rc<AletheTerm>, bool)> {
    args.iter()
        .tuples()
        .map(|(x, y)| match (x, y) {
            (pivot, flag) if flag.is_bool_true() => ((*pivot).clone(), true),
            (pivot, flag) if flag.is_bool_false() => ((*pivot).clone(), false),
            _ => panic!("Pivot are not a tuple of term and bool anymore"),
        })
        .collect_vec()
}

/// Returns a new clause containing all literals of the resolvent premises after the pivot and its negation have been removed.
///
/// convention for the pivot polarity:
/// * If `flag` is `true`, the positive pivot must occur in `clause_left` and its negation in `clause_right`.
/// * If `flag` is `false`, the negated pivot must occur in `clause_left` and the positive pivot in `clause_right`.
///
/// Exactly one occurrence is removed from each side if present; the remaining literals are
/// concatenated in order (left part first, then right part), preserving the original left-to-right
/// order except for the single deletions.
///
/// This function does **not** panic if the pivot is missing; it simply leaves the clause
/// unchanged on that side. (Sanity of pivot presence is enforced in `make_resolution`.
fn remove_pivot_in_clause(
    (pivot, flag): &(Rc<AletheTerm>, bool),
    clause_left: &[Rc<AletheTerm>],
    clause_right: &[Rc<AletheTerm>],
    pool: &mut PrimitivePool,
) -> Vec<Rc<AletheTerm>> {
    let mut duration = Duration::ZERO;

    //FIXME: pivot should be or there is a bug
    if *flag {
        let mut filtered_clause_left = clause_left
            .iter()
            .map(std::clone::Clone::clone)
            .collect_vec();
        let index = filtered_clause_left
            .iter()
            .position(|t| polyeq(pivot, t, &mut duration));

        if let Some(index) = index {
            filtered_clause_left.remove(index);
        }

        let mut filtered_clause_right = clause_right
            .iter()
            .map(std::clone::Clone::clone)
            .collect_vec();
        let index = filtered_clause_right
            .iter()
            .position(|t| polyeq(&term_negated(pivot, pool), t, &mut duration));
        if let Some(index) = index {
            filtered_clause_right.remove(index);
        }

        filtered_clause_left.append(&mut filtered_clause_right);
        filtered_clause_left
    } else {
        let mut filtered_clause_left = clause_left
            .iter()
            .map(std::clone::Clone::clone)
            .collect_vec();
        let index = filtered_clause_left
            .iter()
            .position(|t| polyeq(&term_negated(pivot, pool), t, &mut duration));

        if let Some(index) = index {
            filtered_clause_left.remove(index);
        }

        let mut filtered_clause_right = clause_right
            .iter()
            .map(std::clone::Clone::clone)
            .collect_vec();
        let index = filtered_clause_right
            .iter()
            .position(|t| polyeq(pivot, t, &mut duration));

        if let Some(index) = index {
            filtered_clause_right.remove(index);
        }

        filtered_clause_left.append(&mut filtered_clause_right);
        filtered_clause_left
    }
}

/// Build the Lambdapi proof step that performs binary resolution over a given pivot.
///
///
/// t1: p,A     t2: ¬p,B
/// ---------------------- (:rule resolution :premises (t1 t2) :args (p true))
///    A,B
///
/// This function constructs the application of one of the two resolution lemmas
/// `disj_resolutionN1` or `disj_resolutionN2` in Lambdapi, depending on where the negated
/// occurrence of the pivot appears. The choice follows Carcara’s flag convention:
/// - If `flag_position_pivot` is `true`, the positive pivot is in the **left** premise and the
///   negated pivot is in the **right** premise; `disj_resolutionN2` is applied.
/// - If `flag_position_pivot` is `false`, the negated pivot is in the **left** premise and the
///   positive pivot is in the **right** premise; `disj_resolutionN1` is applied.
///
/// The function:
/// 1) locates the pivot indices `i` and `j` inside the left and right clauses,
/// 2) converts both clauses to Lambdapi terms using `ctx.get_or_convert`,
/// 3) applies the appropriate lemma with the clauses, indices, hypotheses (step names),
///    and trivial introductions of `⊤ᵢ` together with `eq_refl`.
///
/// ```text
/// have t1_t2 : π̇ (a1 ⸬ ...⸬ p ⸬... ⸬ an ⸬ b1 ⸬ ...⸬ ¬ p ⸬... ⸬ bn ⸬ □) {
///     apply disj_resolutionN1
///         (a1 ⸬ ...⸬ p ⸬... ⸬ an ⸬ □)
///         (b1 ⸬ ...⸬ ¬ p ⸬... ⸬ an ⸬ □)
///         i
///         j
///         t1 t2
///         ⊤ᵢ ⊤ᵢ (eq_refl _);
/// };
/// ```
fn make_resolution(
    (pivot, flag_position_pivot): &(Rc<AletheTerm>, bool),
    (left_step_name, left_clause): &(&str, &[Rc<AletheTerm>]),
    (right_step_name, right_clause): &(&str, &[Rc<AletheTerm>]),
    ctx: &mut Context,
    pool: &mut PrimitivePool,
) -> Vec<ProofStep> {
    let hyp_left_arg = Term::TermId((*left_step_name).to_owned());
    let hyp_right_arg = Term::TermId((*right_step_name).to_owned());

    let neg_pivot = term_negated(pivot, pool);
    let mut zero_duration = Duration::ZERO;
    let (i, j) = if *flag_position_pivot {
        let i = left_clause
            .iter()
            .position(|x| polyeq(pivot, x, &mut zero_duration))
            .expect("1");
        let j = right_clause
            .iter()
            .position(|x| polyeq(&neg_pivot, x, &mut zero_duration))
            .expect("2");
        (i, j)
    } else {
        // flag at `false` so negation of the pivot is on the first premise and positive pivot on the 2nd.
        let i = left_clause
            .iter()
            .position(|x| polyeq(&neg_pivot, x, &mut zero_duration))
            .expect("3");
        let j = right_clause
            .iter()
            .position(|x| polyeq(pivot, x, &mut zero_duration))
            .expect("4");
        (i, j)
    };

    let ps = Term::Alethe(LTerm::Clauses(
        left_clause
            .iter()
            .map(|c| ctx.get_or_convert(c).0)
            .collect_vec(),
    ));
    let qs = Term::Alethe(LTerm::Clauses(
        right_clause
            .iter()
            .map(|c| ctx.get_or_convert(c).0)
            .collect_vec(),
    ));

    // apply disj_resolutionN (p_29 ⸬ (p_11 ⸬ (p_10 ⸬ □))) (p_12 ⸬ □) (int2nat 1 ⊤ᵢ) Stdlib.Nat._0 t14_t0 t14_t9 ⊤ᵢ ⊤ᵢ (eq_refl _);
    if *flag_position_pivot {
        vec![ProofStep::Apply(
            terms![
                "disj_resolutionN2".into(),
                ..vec![
                    ps,
                    qs,
                    int2nat(i),
                    int2nat(j),
                    hyp_left_arg,
                    hyp_right_arg,
                    intro_top(),
                    intro_top(),
                    Term::Terms(vec!["eq_refl".into(), Term::Underscore]),
                ]
            ],
            SubProofs(None),
        )]
    } else {
        vec![ProofStep::Apply(
            terms![
                "disj_resolutionN1".into(),
                ..vec![
                    ps,
                    qs,
                    int2nat(i),
                    int2nat(j),
                    hyp_left_arg,
                    hyp_right_arg,
                    intro_top(),
                    intro_top(),
                    Term::Terms(vec!["eq_refl".into(), Term::Underscore]),
                ]
            ],
            SubProofs(None),
        )]
    }
    //left_clause.pos
}

/// Create the negation of a term
#[inline]
fn term_negated(term: &Rc<AletheTerm>, pool: &mut PrimitivePool) -> Rc<AletheTerm> {
    pool.add(AletheTerm::Op(Operator::Not, vec![term.clone()]))
}

/// Create a proof step for the resolution
pub(crate) fn translate_resolution(
    proof_iter: &mut ProofIter<'_>,
    premises: &[(usize, usize)],
    args: &[Rc<AletheTerm>],
    context: &mut Context,
    pool: &mut PrimitivePool,
) -> Vec<ProofStep> {
    let premises = get_premises_clause(proof_iter, premises);

    let pivots = get_pivots_from_args(args);

    let (last_goal_name, _, mut steps) = match premises.as_slice() {
        [h1, h2, tl_premises @ ..] => match pivots.as_slice() {
            [pivot, tl_pivot @ ..] => tl_premises.iter().zip(tl_pivot).fold(
                (
                    format!("{}_{}", h1.0, h2.0),
                    remove_pivot_in_clause(pivot, h1.1, h2.1, pool),
                    vec![ProofStep::Have(
                        format!("{}_{}", h1.0, h2.0),
                        proof(Term::Alethe(LTerm::Clauses(
                            remove_pivot_in_clause(pivot, h1.1, h2.1, pool)
                                .into_iter()
                                .map(|t| context.get_or_convert(&t).0)
                                .collect::<Vec<Term>>(),
                        ))),
                        make_resolution(pivot, &(&h1.0, h1.1), &(&h2.0, h2.1), context, pool),
                    )],
                ),
                |(previous_goal_name, previous_goal, mut proof_steps), (premise, pivot)| {
                    let goal_name = format!("{}_{}", previous_goal_name, premise.0);

                    let current_goal =
                        remove_pivot_in_clause(pivot, previous_goal.as_slice(), premise.1, pool);

                    let resolution = make_resolution(
                        pivot,
                        &(previous_goal_name.clone().as_str(), &previous_goal),
                        &(&premise.0, premise.1),
                        context,
                        pool,
                    );

                    proof_steps.push(ProofStep::Have(
                        goal_name.clone(),
                        proof(Term::Alethe(LTerm::Clauses(
                            current_goal
                                .iter()
                                .map(|t| context.get_or_convert(t).0)
                                .collect::<Vec<Term>>(),
                        ))),
                        resolution,
                    ));

                    (goal_name, current_goal, proof_steps)
                },
            ),
            _ => unreachable!(),
        },
        _ => unreachable!(),
    };

    steps.push(ProofStep::Refine(
        Term::TermId(last_goal_name),
        SubProofs(None),
    ));

    steps
}
