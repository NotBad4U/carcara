//! Linear integer arithmetic: la_generic and the arithmetic RARE
//! rewrites. Mirrors `alethe-lp/lia.lp`.

use rug::Integer;
use crate::translation::lambdapi::*;
use crate::ast::{Operator, Rc, Term as AletheTerm, match_term_err};
use std::ops::Deref;
use crate::ast::Constant;
use crate::ast::match_term;

#[derive(Debug, PartialEq)]
enum Op {
    Eq,
    Lt,
    Gt,
    Ge,
    Le,
}

#[derive(Debug)]
struct ReifiedInequality {
    lhs: Rc<AletheTerm>,
    rhs: Rc<AletheTerm>,
    op: Op,
    neg: bool,
    #[allow(dead_code)]
    name: String, // for debug purposes
}

pub fn gen_proof_la_generic(
    clause: &[Rc<AletheTerm>],
    args: &[Rc<AletheTerm>],
    pool: &mut PrimitivePool,
) -> Vec<ProofStep> {
    let inequalities: Vec<ReifiedInequality> = get_inequalities_from_clause(clause);

    let la_clause = clause
        .iter()
        //.map(|i| inequalitie_with_alias_name(i))
        .map(Term::from)
        .collect_vec();

    // let sets = inequalities.iter().fold(vec![], |mut sets, i| {
    //     sets.push(ProofStep::Set(format!("{}l", i.name), i.lhs.clone().into()));
    //     sets.push(ProofStep::Set(format!("{}r", i.name), i.rhs.clone().into()));
    //     sets
    // });

    let mut proof_la = vec![ProofStep::Apply(Term::from("∨ᵢ₁"), SubProofs(None))];

    proof_la.append(&mut la_generic(inequalities, args, pool).unwrap().0);

    let id_temp_proof = String::from("Hla");

    let ring_computation_proof = ProofStep::Have(
        id_temp_proof.clone(),
        Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(vec![
            Term::Alethe(LTerm::NOr(la_clause)),
        ]))))),
        proof_la,
    );

    let mut proof: Vec<ProofStep> = vec![];

    proof.append(&mut vec![
        ring_computation_proof,
        ProofStep::Simplify(vec![]),
        ProofStep::Rewrite(false, None, "or_identity_r".into(), vec![], SubProofs(None)),
        ProofStep::Apply(unary_clause_to_prf(&id_temp_proof), SubProofs(None)),
    ]);

    proof
}

fn get_inequalities_from_clause(clause: &[Rc<AletheTerm>]) -> Vec<ReifiedInequality> {
    clause
        .iter()
        .enumerate()
        .map(|(i, t)| match t.deref() {
            AletheTerm::Op(Operator::Equals, xs) => ReifiedInequality {
                lhs: xs[0].clone(),
                rhs: xs[1].clone(),
                op: Op::Eq,
                neg: false,
                name: format!("H{}", i),
            },
            AletheTerm::Op(Operator::LessEq, xs) => ReifiedInequality {
                lhs: xs[0].clone(),
                rhs: xs[1].clone(),
                op: Op::Le,
                neg: false,
                name: format!("H{}", i),
            },
            AletheTerm::Op(Operator::LessThan, xs) => ReifiedInequality {
                lhs: xs[0].clone(),
                rhs: xs[1].clone(),
                op: Op::Lt,
                neg: false,
                name: format!("H{}", i),
            },
            AletheTerm::Op(Operator::GreaterThan, xs) => ReifiedInequality {
                lhs: xs[0].clone(),
                rhs: xs[1].clone(),
                op: Op::Gt,
                neg: false,
                name: format!("H{}", i),
            },
            AletheTerm::Op(Operator::GreaterEq, xs) => ReifiedInequality {
                lhs: xs[0].clone(),
                rhs: xs[1].clone(),
                op: Op::Ge,
                neg: false,
                name: format!("H{}", i),
            },
            AletheTerm::Op(Operator::Not, t) => match t.first().unwrap().deref() {
                AletheTerm::Op(Operator::Equals, xs) => ReifiedInequality {
                    lhs: xs[0].clone(),
                    rhs: xs[1].clone(),
                    op: Op::Eq,
                    neg: true,
                    name: format!("H{}", i),
                },
                AletheTerm::Op(Operator::LessEq, xs) => ReifiedInequality {
                    lhs: xs[0].clone(),
                    rhs: xs[1].clone(),
                    op: Op::Le,
                    neg: true,
                    name: format!("H{}", i),
                },
                AletheTerm::Op(Operator::LessThan, xs) => ReifiedInequality {
                    lhs: xs[0].clone(),
                    rhs: xs[1].clone(),
                    op: Op::Lt,
                    neg: true,
                    name: format!("H{}", i),
                },
                AletheTerm::Op(Operator::GreaterThan, xs) => ReifiedInequality {
                    lhs: xs[0].clone(),
                    rhs: xs[1].clone(),
                    op: Op::Gt,
                    neg: true,
                    name: format!("H{}", i),
                },
                AletheTerm::Op(Operator::GreaterEq, xs) => ReifiedInequality {
                    lhs: xs[0].clone(),
                    rhs: xs[1].clone(),
                    op: Op::Ge,
                    neg: true,
                    name: format!("H{}", i),
                },
                _ => unreachable!(),
            },
            _ => unreachable!(),
        })
        .collect_vec()
}

fn sum_hyps(prefix: &str, suffix: &str, start: usize, end: usize) -> String {
    let s = (start..end)
        .map(|i| format!("{}{}{}", prefix, i, suffix))
        .collect_vec();
    s.join(" + ")
}

// Kept fallible like the other rule handlers; real error paths replace the remaining
// panics in a later hardening pass.
#[allow(clippy::unnecessary_wraps)]
fn la_generic(
    inequalities: Vec<ReifiedInequality>,
    args: &[Rc<AletheTerm>],
    pool: &mut PrimitivePool,
) -> TradResult<Proof> {
    let mut inequalities = inequalities;

    let args = args
        .iter()
        .map(|a| match a.deref() {
            AletheTerm::Const(c) => c,
            _ => unreachable!(),
        })
        .collect_vec();

    // step 1: negates the literal
    // If 𝜑 = s1 > s2, then let 𝜑 ∶= s1 ≤ s2.
    // If 𝜑 = s1 ≥ s2 , then let 𝜑 ∶= s1 < s2 .
    // If 𝜑 = s1 < s2 , then let 𝜑 ∶= s1 ≥ s2 .
    // If 𝜑 = s1 ≤ s2 , then let 𝜑 ∶= s1 > s2 .
    //FIXME: only done for Eq for now
    // let mut step1 = vec![];

    let mut step1 = inequalities
        .iter()
        .enumerate()
        .filter(|(_, l)| !l.neg && l.op != Op::Eq)
        .map(|(i, l)| {
            let mut pattern: Vec<String> = vec!["_".to_owned(); inequalities.len()];
            pattern[i] = "x".to_owned();
            let pattern_with_or: String =
                itertools::intersperse(pattern, " ∨ ".to_owned()).collect();
            match l.op {
                Op::Lt => ProofStep::Rewrite(
                    false,
                    Some(format!("[x in {}]", pattern_with_or)),
                    "Zlt_not_ge".into(),
                    vec![],
                    SubProofs(None),
                ),
                Op::Le => ProofStep::Rewrite(
                    false,
                    Some(format!("[x in {}]", pattern_with_or)),
                    "Zle_not_gt".into(),
                    vec![],
                    SubProofs(None),
                ),
                Op::Ge => ProofStep::Rewrite(
                    false,
                    Some(format!("[x in {}]", pattern_with_or)),
                    "Zge_not_lt".into(),
                    vec![],
                    SubProofs(None),
                ),
                Op::Gt => ProofStep::Rewrite(
                    false,
                    Some(format!("[x in {}]", pattern_with_or)),
                    "Zgt_not_le".into(),
                    vec![],
                    SubProofs(None),
                ),
                Op::Eq => unreachable!("Eq inequalities are filtered out above"),
            }
        })
        .collect_vec();

    for i in &mut inequalities {
        if !i.neg {
            i.op = match i.op {
                Op::Eq => Op::Eq,
                Op::Lt => Op::Ge,
                Op::Le => Op::Gt,
                Op::Gt => Op::Le,
                Op::Ge => Op::Lt,
            };
            i.neg = true; // the literal have been negate
        }
    }

    //println!("Step 1 {:?}", inequalities);

    // Step normalize < and ≤. The algorithm expect to work only with ⋈ = { >, = , ≥ }
    // If 𝜑 = a < b then 𝜑 = ~ a > ~ b
    // If 𝜑 = a ≤ b then 𝜑 = ~ a ≥ ~ b
    let mut normalize_step = vec![];

    for i in &mut inequalities {
        if i.op == Op::Lt {
            i.lhs = pool.add(AletheTerm::Op(Operator::Sub, vec![i.lhs.clone()]));
            i.rhs = pool.add(AletheTerm::Op(Operator::Sub, vec![i.rhs.clone()]));
            i.op = Op::Gt;
            normalize_step.push(ProofStep::Try(Box::new(ProofStep::Rewrite(
                false,
                None,
                "Zinv_lt_eq".into(),
                vec![],
                SubProofs(None),
            ))));
        }
        if i.op == Op::Le {
            i.lhs = pool.add(AletheTerm::Op(Operator::Sub, vec![i.lhs.clone()]));
            i.rhs = pool.add(AletheTerm::Op(Operator::Sub, vec![i.rhs.clone()]));
            i.op = Op::Ge;
            normalize_step.push(ProofStep::Try(Box::new(ProofStep::Rewrite(
                false,
                None,
                "Zinv_le_eq".into(),
                vec![],
                SubProofs(None),
            ))));
        }
    }

    //println!("Step Normalize {:?}", inequalities);

    // step 3:
    let mut step3 = inequalities
        .iter()
        .map(|i| match i.op {
            Op::Eq => ProofStep::Rewrite(
                false,
                None,
                "Z_diff_eq_Z0_eq".into(),
                vec![i.lhs.clone().into(), i.rhs.clone().into()],
                SubProofs(None),
            ),
            Op::Ge => ProofStep::Rewrite(
                false,
                None,
                "Z_diff_geq_Z0_eq".into(),
                vec![i.lhs.clone().into(), i.rhs.clone().into()],
                SubProofs(None),
            ),
            Op::Gt => ProofStep::Rewrite(
                false,
                None,
                "Z_diff_gt_Z0_eq".into(),
                vec![i.lhs.clone().into(), i.rhs.clone().into()],
                SubProofs(None),
            ),
            _ => unreachable!(),
        })
        .collect_vec();

    for i in &mut inequalities {
        i.lhs = pool.add(AletheTerm::Op(
            Operator::Sub,
            vec![i.lhs.clone(), i.rhs.clone()],
        ));
        i.rhs = pool.add(AletheTerm::Const(Constant::Integer(Integer::from(0))));
    }

    //println!("Step 3 {:?}", inequalities);

    // Now 𝜑 has the form s1 ⋈ d. If all variables in s1 are integer sorted: replace ⋈ d according to the table below.
    let mut step4 = inequalities
        .iter()
        .filter(|i| matches!(i.op, Op::Gt))
        .map(|i| {
            ProofStep::Rewrite(
                false,
                None,
                "Zgt_le_succ_r_eq".into(),
                vec![i.lhs.clone().into(), i.rhs.clone().into()],
                SubProofs(None),
            )
        })
        .collect_vec();

    for i in &mut inequalities {
        if i.op == Op::Gt {
            let one = pool.add(AletheTerm::Const(Constant::Integer(Integer::from(1))));
            i.rhs = pool.add(AletheTerm::Op(Operator::Add, vec![i.rhs.clone(), one]));
            i.op = Op::Ge;
        }
    }

    //println!("Step 4 {:?}", inequalities);

    // step 5
    // If ⋈ is ≈ replace l with i ∈ 0..m by
    // ∑ a × ci × ti ≈ a × d,
    // otherwise replace it by ∑ |a| × ci × ti ≈ |a| × d.
    let mut step5 = vec![];
    let mut rw_args = inequalities
        .iter()
        .zip(args.iter())
        .map(|(i, c)| match i {
            ReifiedInequality { lhs, rhs, op: Op::Eq, .. } => {
                let c: Integer = match c {
                    Constant::Integer(i) => i.clone(),
                    Constant::Real(r) => r.clone().into_numer_denom().0,
                    _ => unreachable!(),
                };
                let lhs = Term::from(lhs);
                let rhs = Term::from(rhs);
                ProofStep::Rewrite(
                    false,
                    None,
                    "Zmult_eq_compat_eq".into(),
                    vec![Term::Int(c.clone()), lhs, rhs],
                    SubProofs(None),
                )
            }
            ReifiedInequality { lhs, rhs, .. } => {
                let c: Integer = match c {
                    Constant::Integer(i) => i.clone(),
                    Constant::Real(r) => r.clone().into_numer_denom().0.clone(),
                    _ => unreachable!(),
                };
                let lhs = Term::from(lhs);
                let rhs = Term::from(rhs);
                ProofStep::Rewrite(
                    false,
                    None,
                    "Zmult_ge_compat_eq".into(),
                    vec![Term::Int(c.clone()), lhs, rhs],
                    SubProofs(None),
                )
            }
        })
        .collect_vec();
    step5.append(&mut rw_args);

    for (i, arg) in inequalities.iter_mut().zip(args) {
        let c = match arg.to_owned() {
            Constant::Integer(c) => c,
            Constant::Real(c) => c.into_numer_denom().0,
            _ => unreachable!(),
        };
        let c_const = pool.add(AletheTerm::Const(Constant::Integer(c.clone())));
        i.lhs = pool.add(AletheTerm::Op(
            Operator::Mult,
            vec![c_const.clone(), i.lhs.clone()],
        ));
        i.rhs = pool.add(AletheTerm::Op(Operator::Mult, vec![c_const, i.rhs.clone()]));
    }

    step5.push(ProofStep::Try(Box::new(ProofStep::Rewrite(
        false,
        None,
        "Z_eq_antisym".into(),
        vec![],
        SubProofs(None),
    ))));

    // Step 2 If 𝜑 = ¬(s1 ⋈ s2), then let 𝜑 ∶= s2 ⋈ s2. We interpret this step as moving literals in the context
    let mut step2 = inequalities
        .iter()
        .enumerate()
        .map(|(counter, _)| {
            vec![
                //rewrite imp_eq_or; assume H1;
                ProofStep::Rewrite(false, None, "imp_eq_or".into(), vec![], SubProofs(None)),
                ProofStep::Assume(vec![format!("H{}", counter)]),
            ]
        })
        .collect_vec();
    step2.pop();
    step2.append(&mut vec![vec![ProofStep::Assume(vec![format!(
        "H{}",
        step2.len()
    )])]]);

    // Finally, the sum of the resulting literals is trivially contradictory.
    // The sum on the left-hand side is 0 and the right-hand side is > 0 (or ≥ 0 if ⋈ is >).
    //let sum =  inequalities.iter().(|acc, c.| acc = AletheTerm::Op(Operator::Add, );
    let mut sets = inequalities
        .iter()
        .enumerate()
        .map(|(counter, i)| {
            vec![
                ProofStep::Set(format!("H{}l'", counter), i.lhs.clone().into()),
                ProofStep::Set(format!("H{}r'", counter), i.rhs.clone().into()),
            ]
        })
        .collect_vec()
        .concat();

    let ine_len = inequalities.len();

    //HACK: to be faster we generate the goal has a constant string
    let left_sum = Term::from(
        sum_hyps("H", "l'", 0, ine_len), // inequalities
                                         //     .iter()
                                         //     .enumerate()
                                         //     .map(|(i, _)| format!("H{}l'", i))
                                         //     .join(" + "),
    );

    let right_sum = Term::from(
        // inequalities
        //     .iter()
        //     .enumerate()
        //     .map(|(i, _)| format!("H{}r'", i))
        //    .join(" + "),
        sum_hyps("H", "r'", 0, ine_len),
    );

    let left_prefix = "l";
    let right_prefix = "r";

    sets.push(ProofStep::Set(left_prefix.to_owned(), left_sum));
    sets.push(ProofStep::Set(right_prefix.to_owned(), right_sum));

    let left_prefix_term = Term::from(left_prefix);
    let right_prefix_term = Term::from(right_prefix);

    //FIXME: support also Gt and Eq
    let final_sum = Term::Terms(vec![
        left_prefix_term.clone(),
        Term::from("≥"),
        right_prefix_term.clone(),
    ]);

    // We want to generate (Zsum_geq_s H0l' H0r' (H1l' + H2l') (H1r' + H2r') H0 (Zsum_geq_s H1l' H1r' H2l' H2r' H1 H2));
    let mut pack: Term = Term::Terms(vec![
        "Zsum_geq_s".into(),
        format!("H{}l'", ine_len - 2).into(),
        format!("H{}r'", ine_len - 2).into(),
        format!("H{}l'", ine_len - 1).into(),
        format!("H{}r'", ine_len - 1).into(),
        format!("H{}", ine_len - 2).into(),
        format!("H{}", ine_len - 1).into(),
    ]);
    inequalities
        .iter()
        .enumerate()
        .rev()
        .skip(2)
        .for_each(|(i, _)| {
            pack = Term::Terms(vec![
                "Zsum_geq_s".into(),
                format!("H{}l'", i).into(),
                format!("H{}r'", i).into(),
                Term::Terms(vec![Term::from(sum_hyps("H", "l'", i + 1, ine_len))]),
                Term::Terms(vec![Term::from(sum_hyps("H", "r'", i + 1, ine_len))]),
                format!("H{}", i).into(),
                pack.clone(),
            ]);
        });

    let sum_hyp_name = "sum";

    let contradiction = ProofStep::Have(
        sum_hyp_name.to_owned(),
        Term::Alethe(LTerm::ClassicProof(Box::new(final_sum))),
        vec![ProofStep::Refine(pack, SubProofs(None))],
    );

    let mut proof = vec![];

    proof.append(&mut step1);
    proof.append(&mut normalize_step);
    proof.append(&mut step3);
    proof.append(&mut step4);
    proof.append(&mut step5);
    proof.append(&mut step2.concat());
    proof.append(&mut sets);

    proof.push(contradiction);

    proof.push(ProofStep::Refine(
        terms![Term::from(sum_hyp_name), Term::Underscore],
        SubProofs(None),
    ));

    proof.push(ProofStep::Rewrite(
        true,
        None,
        Term::from("reify_correct"),
        vec![left_prefix_term.clone()],
        SubProofs(None),
    ));
    proof.push(ProofStep::Rewrite(
        true,
        None,
        Term::from("reify_correct"),
        vec![right_prefix_term.clone()],
        SubProofs(None),
    ));

    let left_prefix_p = format!("{}'", left_prefix);
    let right_prefix_p = format!("{}'", right_prefix);

    proof.push(ProofStep::Set(
        left_prefix_p.clone(),
        Term::Terms(vec![Term::from("reify"), left_prefix_term.clone()]),
    ));
    proof.push(ProofStep::Set(
        right_prefix_p.clone(),
        Term::Terms(vec![Term::from("reify"), right_prefix_term.clone()]),
    ));

    let left_prefix_term = Term::from(left_prefix_p.clone());
    let right_prefix_term = Term::from(right_prefix_p.clone());

    proof.push(ProofStep::Rewrite(
        false,
        None,
        Term::from("eta_prod"),
        vec![left_prefix_term.clone()],
        SubProofs(None),
    ));
    proof.push(ProofStep::Rewrite(
        false,
        None,
        Term::from("eta_prod"),
        vec![right_prefix_term.clone()],
        SubProofs(None),
    ));

    proof.push(ProofStep::Rewrite(
        true,
        None,
        Term::from("norm_correct"),
        vec![
            Term::Terms(vec![left_prefix_term.clone(), Term::from("₁")]),
            Term::Terms(vec![left_prefix_term, Term::from("₂")]),
        ],
        SubProofs(None),
    ));

    proof.push(ProofStep::Refine(intro_top(), SubProofs(None)));

    Ok(Proof(proof))
}

/// Rule 13: `la_disequality`
/// `𝑡1 ≈ 𝑡2 ∨ ¬(𝑡1 ≤ 𝑡2) ∨ ¬(𝑡2 ≤ 𝑡1)`
///
/// is translated into the script:
///
/// ```text
/// refine la_disequality t1 t2;
/// ```
pub fn translate_la_disequality(clause: &[Rc<AletheTerm>]) -> TradResult<Proof> {
    let mut proof = vec![];

    let eq_t1_t2 = match_term_err!((or ...) = &clause[0])
        .unwrap()
        .first()
        .unwrap();

    let (t1, t2): (Term, Term) = match_term_err!((= t1 t2) = eq_t1_t2)
        .map(|(t1, t2)| (t1.into(), t2.into()))
        .expect("No equality found in la_disequality?");

    proof.push(ProofStep::Refine(
        terms!["la_disequality".into(), t1, t2],
        SubProofs(None),
    ));

    Ok(Proof(proof))
}

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

/// Provide a proof term for `evaluate` rule that fold numeric constant.
/// For example:
/// ```text
/// (step tj (cl (= (>= 0 0) true)) :rule rare_rewrite :args ("evaluate"))
/// ```
pub(super) fn translate_evaluate_linear_arith() -> Vec<ProofStep> {
    vec![ProofStep::Admit]
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
pub(super) fn translate_arith_poly_norm(clause: &[Rc<AletheTerm>]) -> Vec<ProofStep> {
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
    let (left, _) = match_term!((= l r) = clause[0]).expect("no equality");
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
