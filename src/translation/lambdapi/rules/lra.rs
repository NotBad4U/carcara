//! Linear real arithmetic: `la_generic` over the reals. Mirrors `alethe-lp/lra.lp`.
//! The arithmetic RARE rewrites over the reals are the `RareLra` entries of
//! `rare/mod.rs`, and `la_disequality`/`la_totality` reuse the `lia.rs` scripts,
//! since `lra.lp` declares those lemmas under the same names.
//!
//! The generator follows `lia.rs` step for step, with two differences the carrier
//! forces. Step 4 of the rule (`s > d` into `s ≥ d + 1`) only holds over the
//! integers and is skipped. And the tail differs: on ℤ the contradictory sum
//! `l < r` computes to ⊤ once `l` is normalised, but `≤ᵣ` does not compute, so
//! every literal keeps `zero` on its right-hand side, the sum is `l ⋈ zero`, `l`
//! is rewritten into its normal form with `reflect` (its premise holds by
//! computation on the concrete `l`, so no lemma reduces `rfy` on a variable), and
//! `val_lt_zero`/`val_le_zero` decide the sign of that normal form.

use super::lia::{Op, ReifiedInequality, get_inequalities_from_clause, sum_hyps_with};
use crate::ast::{Constant, Operator, Rc, Term as AletheTerm, match_term};
use crate::translation::lambdapi::*;
use rug::Rational;

/// `＋ᵣ` is right-associative, so `a ＋ᵣ b ＋ᵣ c` is `a ＋ᵣ (b ＋ᵣ c)`: the shape the
/// sum lemmas nest in.
const ADD: &str = " ＋ᵣ ";

pub fn gen_proof_la_generic(
    clause: &[Rc<AletheTerm>],
    args: &[Rc<AletheTerm>],
    pool: &mut PrimitivePool,
) -> Vec<ProofStep> {
    let inequalities = get_inequalities_from_clause(clause);

    let la_clause = clause.iter().map(Term::from).collect_vec();

    let mut proof_la = vec![ProofStep::Apply(Term::from("∨ᵢ₁"), SubProofs(None))];
    proof_la.append(&mut la_generic(inequalities, args, pool).0);

    let id_temp_proof = String::from("Hla");

    let farkas_proof = ProofStep::Have(
        id_temp_proof.clone(),
        Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(vec![
            Term::Alethe(LTerm::NOr(la_clause)),
        ]))))),
        proof_la,
    );

    // The step's clause as one disjunction: `simplify` unfolds `π̇ (a ⸬ b ⸬ □)`
    // into `π (a ∨ b ∨ ⊥)`, and `or_identity_r` drops the `⊥`.
    vec![
        farkas_proof,
        ProofStep::Simplify(vec![]),
        ProofStep::Rewrite(false, None, "or_identity_r".into(), vec![], SubProofs(None)),
        ProofStep::Apply(unary_clause_to_prf(&id_temp_proof), SubProofs(None)),
    ]
}

/// The step's `:args`, one coefficient per literal: a numeral, possibly negated.
fn coefficients(args: &[Rc<AletheTerm>]) -> Vec<Rational> {
    fn numeral(a: &AletheTerm) -> Rational {
        match a {
            AletheTerm::Const(Constant::Real(r)) => r.clone(),
            AletheTerm::Const(Constant::Integer(i)) => Rational::from(i),
            AletheTerm::Op(Operator::Sub, xs) if xs.len() == 1 => -numeral(&xs[0]),
            _ => unreachable!("la_generic coefficients are numerals"),
        }
    }
    args.iter().map(|a| numeral(a)).collect_vec()
}

fn la_generic(
    mut inequalities: Vec<ReifiedInequality>,
    args: &[Rc<AletheTerm>],
    pool: &mut PrimitivePool,
) -> Proof {
    let coefficients = coefficients(args);
    let n = inequalities.len();
    let hyp_name = |i: usize| format!("H{i}");
    let side_name = |i: usize| format!("H{i}l'");

    // Step 1: a positive literal `s1 ⋈ s2` is the negation of its converse.
    // If 𝜑 = s1 > s2, then let 𝜑 ∶= ¬(s1 ≤ s2), and so on. Equalities are
    // never positive in an `la_generic` clause.
    let mut step1 = inequalities
        .iter()
        .enumerate()
        .filter(|(_, l)| !l.neg && l.op != Op::Eq)
        .map(|(i, l)| {
            let mut pattern: Vec<String> = vec!["_".to_owned(); n];
            pattern[i] = "x".to_owned();
            let pattern_with_or: String =
                itertools::intersperse(pattern, " ∨ ".to_owned()).collect();
            let lemma = match l.op {
                Op::Lt => "Rlt_not_ge",
                Op::Le => "Rle_not_gt",
                Op::Ge => "Rge_not_lt",
                Op::Gt => "Rgt_not_le",
                Op::Eq => unreachable!("Eq inequalities are filtered out above"),
            };
            ProofStep::Rewrite(
                false,
                Some(format!("[x in {}]", pattern_with_or)),
                lemma.into(),
                vec![],
                SubProofs(None),
            )
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
            i.neg = true; // the literal has been negated
        }
    }

    // Normalise `<` and `≤` into `>` and `≥`, the only relations the sum needs
    // besides `=`: `a < b` is `—ᵣ a > —ᵣ b`. `try`, since a repeated literal is
    // rewritten with the first.
    let mut normalize_step = vec![];
    for i in &mut inequalities {
        let flipped = match i.op {
            Op::Lt => Some(("Rinv_lt_eq", Op::Gt)),
            Op::Le => Some(("Rinv_le_eq", Op::Ge)),
            _ => None,
        };
        if let Some((lemma, op)) = flipped {
            i.lhs = pool.add(AletheTerm::Op(Operator::Sub, vec![i.lhs.clone()]));
            i.rhs = pool.add(AletheTerm::Op(Operator::Sub, vec![i.rhs.clone()]));
            i.op = op;
            normalize_step.push(ProofStep::Try(Box::new(ProofStep::Rewrite(
                false,
                None,
                lemma.into(),
                vec![],
                SubProofs(None),
            ))));
        }
    }

    // Step 3: move everything to the left-hand side, `s1 ⋈ s2` into
    // `s1 −ᵣ s2 ⋈ zero`. From here only the left-hand sides are tracked; the
    // right-hand side stays `zero` to the end.
    let mut step3 = inequalities
        .iter()
        .map(|i| {
            let lemma = match i.op {
                Op::Eq => "R_diff_eq_zero_eq",
                Op::Ge => "R_diff_geq_zero_eq",
                Op::Gt => "R_diff_gt_zero_eq",
                Op::Lt | Op::Le => unreachable!("normalised above"),
            };
            ProofStep::Rewrite(
                false,
                None,
                lemma.into(),
                vec![i.lhs.clone().into(), i.rhs.clone().into()],
                SubProofs(None),
            )
        })
        .collect_vec();

    let mut sides: Vec<Term> = inequalities
        .iter()
        .map(|i| {
            pool.add(AletheTerm::Op(
                Operator::Sub,
                vec![i.lhs.clone(), i.rhs.clone()],
            ))
            .into()
        })
        .collect_vec();

    // Step 4, `s > d` into `s ≥ d + 1`, is for integer-sorted literals only.

    // Step 5: scale literal i by its coefficient, `a` for an equality and `|a|`
    // otherwise. The side condition -- `c ≠ zero`, resp. `zero <ᵣ c` -- is
    // `lit_ne_zero`/`lit_pos` on the numerals, whose hypothesis computes to ⊤.
    let mut step5 = vec![];
    for ((i, c), side) in inequalities.iter().zip(&coefficients).zip(sides.iter_mut()) {
        let c = if i.op == Op::Eq { c.clone() } else { c.clone().abs() };
        let (lemma, condition) = match i.op {
            Op::Eq => ("Rmult_eq_compat_zero_eq", "lit_ne_zero"),
            Op::Gt => ("Rmult_gt_compat_zero_eq", "lit_pos"),
            _ => ("Rmult_ge_compat_zero_eq", "lit_pos"),
        };
        let condition = Term::Terms(vec![
            condition.into(),
            Term::Int(c.numer().clone()),
            Term::Pos(c.denom().clone()),
            intro_top(),
        ]);
        step5.push(ProofStep::Rewrite(
            false,
            None,
            lemma.into(),
            vec![Term::Real(c.clone()), side.clone(), condition],
            SubProofs(None),
        ));
        *side = Term::Terms(vec![Term::Real(c), "*ᵣ".into(), side.clone()]);
    }

    // Step 2: `¬𝜓0 ∨ … ∨ ¬𝜓n` is `𝜓0 ⇒ … ⇒ 𝜓n ⇒ ⊥`; each literal becomes a
    // hypothesis.
    let mut step2 = vec![];
    for i in 0..n {
        if i + 1 < n {
            step2.push(ProofStep::Rewrite(false, None, "imp_eq_or".into(), vec![], SubProofs(None)));
        }
        step2.push(ProofStep::Assume(vec![hyp_name(i)]));
    }

    // Name the scaled left-hand sides and their sum.
    let mut sets = sides
        .iter()
        .enumerate()
        .map(|(i, side)| ProofStep::Set(side_name(i), side.clone()))
        .collect_vec();
    let l = "l";
    sets.push(ProofStep::Set(l.to_owned(), Term::from(sum_hyps_with(ADD, "H", "l'", 0, n))));

    // The hypothesis `Hi` as a proof of `Hil' ⋈ zero`: an equality literal is
    // weakened with `R_eq_ge`.
    let strict = |i: usize| inequalities[i].op == Op::Gt;
    let hyp = |i: usize| -> Term {
        if inequalities[i].op == Op::Eq {
            Term::Terms(vec!["R_eq_ge".into(), side_name(i).into(), hyp_name(i).into()])
        } else {
            hyp_name(i).into()
        }
    };

    // Sum the hypotheses from the right, the lemma chosen by the strictness of
    // each side: (Rsum0_gt_ge H0l' (H1l' ＋ᵣ H2l') H0 (Rsum0_ge_ge H1l' H2l' H1 H2)).
    let mut pack = hyp(n - 1);
    let mut any_strict = strict(n - 1);
    for i in (0..n - 1).rev() {
        let lemma = match (strict(i), any_strict) {
            (true, true) => "Rsum0_gt_gt",
            (true, false) => "Rsum0_gt_ge",
            (false, true) => "Rsum0_ge_gt",
            (false, false) => "Rsum0_ge_ge",
        };
        pack = Term::Terms(vec![
            lemma.into(),
            side_name(i).into(),
            Term::Terms(vec![Term::from(sum_hyps_with(ADD, "H", "l'", i + 1, n))]),
            hyp(i),
            pack,
        ]);
        any_strict |= strict(i);
    }

    let sum_hyp_name = "sum";
    let relation = if any_strict { ">ᵣ" } else { "≥ᵣ" };
    let contradiction = ProofStep::Have(
        sum_hyp_name.to_owned(),
        Term::Alethe(LTerm::ClassicProof(Box::new(Term::Terms(vec![
            l.into(),
            relation.into(),
            "zero".into(),
        ])))),
        vec![ProofStep::Refine(pack, SubProofs(None))],
    );

    let mut proof = vec![];

    proof.append(&mut step1);
    proof.append(&mut normalize_step);
    proof.append(&mut step3);
    proof.append(&mut step5);
    proof.append(&mut step2);
    proof.append(&mut sets);

    proof.push(contradiction);

    // `l ⋈ zero` against its negation, which the normal form of `l` decides: a
    // strict sum leaves `l ≤ᵣ zero` to prove, a non-strict one `l <ᵣ zero`.
    let (absurd, decide) = if any_strict {
        ("Rgt_le_absurd", "val_le_zero")
    } else {
        ("Rge_lt_absurd", "val_lt_zero")
    };
    proof.push(ProofStep::Refine(
        Term::Terms(vec![absurd.into(), l.into(), Term::Underscore, sum_hyp_name.into()]),
        SubProofs(None),
    ));
    // `l = val (norm_speed (lin (reify l ₁)) ‚ reify l ₂)`, by `reflect` on the
    // reification of `l` itself: its premise `denote (reify l ₁) (reify l ₂) = l`
    // is `eq_refl l` up to computation.
    let reify = |proj: &str| Term::Terms(vec!["reify".into(), l.into(), proj.into()]);
    proof.push(ProofStep::Rewrite(
        false,
        None,
        Term::from("reflect"),
        vec![
            reify("₁"),
            reify("₂"),
            l.into(),
            Term::Terms(vec!["eq_refl".into(), l.into()]),
        ],
        SubProofs(None),
    ));
    proof.push(ProofStep::Refine(
        Term::Terms(vec![
            decide.into(),
            Term::Terms(vec!["norm_speed".into(), Term::Terms(vec!["lin".into(), reify("₁")])]),
            reify("₂"),
            intro_top(),
        ]),
        SubProofs(None),
    ));

    Proof(proof)
}

/// A rational as `alethe.rat` writes it, `n / d`: for the lemmas that take the
/// numeral rather than the literal `lit (n / d)`.
fn rat(r: &Rational) -> Term {
    Term::Terms(vec![Term::Int(r.numer().clone()), "/".into(), Term::Pos(r.denom().clone())])
}

/// `zero <ᵣ lit c` for a positive numeral: `lit_pos n d ⊤ᵢ`, whose hypothesis
/// `0 < n` computes.
fn lit_pos_proof(c: &Rational) -> Term {
    terms!["lit_pos".into(), Term::Int(c.numer().clone()), Term::Pos(c.denom().clone()), intro_top()]
}

/// `lit c ≠ zero` for a non-zero numeral: `lit_ne_zero n d ⊤ᵢ`.
fn lit_ne_zero_proof(c: &Rational) -> Term {
    terms!["lit_ne_zero".into(), Term::Int(c.numer().clone()), Term::Pos(c.denom().clone()), intro_top()]
}

/// `lit c <ᵣ zero` for a negative numeral: `lit_neg_lt_zero p d` on `|n| = p`.
fn lit_neg_proof(c: &Rational) -> Term {
    terms!["lit_neg_lt_zero".into(), Term::Pos(c.numer().clone().abs()), Term::Pos(c.denom().clone())]
}

/// `t = s` for two linear real terms denoting the same polynomial, by
/// reflection: both are reified in one atom environment, so that an atom has
/// the same index on either side, normalised with canonical coefficients
/// (`reflect_canon`), and the two normal forms are then convertible. Nothing
/// here depends on the goal's syntax, so it is unaffected by term sharing or
/// by a `simplify` of the goal. The script for `poly_simp` and for the equality
/// case of `evaluate`.
fn poly_eq_steps(t: Term, s: Term) -> Vec<ProofStep> {
    let env = "env";
    let reify_in_env = |x: &Term| terms!["rfy".into(), env.into(), x.clone(), "₁".into()];
    let reflect = |x: &Term| {
        terms![
            "reflect_canon".into(),
            reify_in_env(x),
            env.into(),
            x.clone(),
            terms!["eq_refl".into(), x.clone()]
        ]
    };
    vec![
        ProofStep::Set(
            env.to_owned(),
            terms!["rfy".into(), terms!["reify".into(), t.clone(), "₂".into()], s.clone(), "₂".into()],
        ),
        ProofStep::Refine(
            terms![
                "eq_trans".into(),
                t.clone(),
                Term::Underscore,
                s.clone(),
                reflect(&t),
                terms!["eq_sym".into(), reflect(&s)]
            ],
            SubProofs(None),
        ),
    ]
}

/// `poly_simp`: `(= t s)` for `t` and `s` the same polynomial over ℝ.
pub fn translate_poly_simp(clause: &[Rc<AletheTerm>]) -> TradResult<Proof> {
    let (t, s) = match_term!((= t s) = clause[0]).ok_or(TranslatorError::PremisesError)?;
    let mut proof = vec![ProofStep::Apply(Term::from("∨ᵢ₁"), SubProofs(None))];
    proof.extend(poly_eq_steps(t.into(), s.into()));
    Ok(Proof(proof))
}

/// The equality case of `evaluate`, `(= t c)` with `t` a constant expression:
/// the same reflection as `poly_simp`, under the `apply ∨ᵢ₁` the caller emits.
pub(crate) fn evaluate_equality(t: Term, s: Term) -> Vec<ProofStep> {
    poly_eq_steps(t, s)
}

/// `poly_simp_rel`: from `c₁·(x₁ − x₂) = c₂·(y₁ − y₂)`, the relations
/// `x₁ ⋈ x₂` and `y₁ ⋈ y₂` are the same proposition. `lra.lp`'s `poly_rel_eq`
/// takes any non-zero coefficients, the inequalities need coefficients of the
/// same sign (`_pos`/`_neg`), like the checker requires; the side conditions
/// are decided on the numerals.
pub fn translate_poly_simp_rel(
    clause: &[Rc<AletheTerm>],
    premise: &(String, &[Rc<AletheTerm>]),
) -> TradResult<Proof> {
    let unsupported = || TranslatorError::UnsupportedRule("poly_simp_rel".to_owned());
    let prem = premise.1.first().ok_or(TranslatorError::PremisesError)?;
    let (c1, xs, c2, ys) = match_term!((= (* c1 xs) (* c2 ys)) = prem).ok_or_else(unsupported)?;
    let (x1, x2) = match_term!((- x1 x2) = xs).ok_or_else(unsupported)?;
    let (y1, y2) = match_term!((- y1 y2) = ys).ok_or_else(unsupported)?;
    let (c1, c2) = (
        c1.as_signed_number().ok_or_else(unsupported)?,
        c2.as_signed_number().ok_or_else(unsupported)?,
    );
    let (l, _) = match_term!((= l r) = clause[0]).ok_or_else(unsupported)?;
    let (op, _) = l.as_op().ok_or_else(unsupported)?;
    let rel = match op {
        Operator::Equals => None,
        Operator::LessEq => Some("le"),
        Operator::LessThan => Some("lt"),
        Operator::GreaterEq => Some("ge"),
        Operator::GreaterThan => Some("gt"),
        _ => return Err(unsupported()),
    };
    let (lemma, h1, h2) = match rel {
        None => ("poly_rel_eq".to_owned(), lit_ne_zero_proof(&c1), lit_ne_zero_proof(&c2)),
        Some(rel) if c1.is_positive() && c2.is_positive() => {
            (format!("poly_rel_{rel}_pos"), lit_pos_proof(&c1), lit_pos_proof(&c2))
        }
        Some(rel) if c1.is_negative() && c2.is_negative() => {
            (format!("poly_rel_{rel}_neg"), lit_neg_proof(&c1), lit_neg_proof(&c2))
        }
        Some(_) => return Err(unsupported()),
    };
    Ok(Proof(vec![
        ProofStep::Apply(Term::from("∨ᵢ₁"), SubProofs(None)),
        ProofStep::Refine(
            terms![
                Term::from(lemma),
                Term::Real(c1),
                Term::from(x1),
                Term::from(x2),
                Term::Real(c2),
                Term::from(y1),
                Term::from(y2),
                h1,
                h2,
                unary_clause_to_prf(&premise.0)
            ],
            SubProofs(None),
        ),
    ]))
}

/// `evaluate` on a comparison of two real numerals, `(= (a ⋈ b) true|false)`:
/// `lit_le_dec`/`lit_lt_dec`/`lit_ne_dec` decide `lit a ⋈ lit b` on the sign of
/// `b 𝕢- a`, which computes, and `eq_⊤_intro`/`eq_⊥_intro` turn the verdict
/// into the equation. `≥ᵣ`, `>ᵣ` and the negations unfold to `≤ᵣ`/`<ᵣ` by
/// definition, so every case is one of the three deciders, possibly under a
/// double negation.
pub(crate) fn evaluate_comparison(
    op: Operator,
    a: &Rational,
    b: &Rational,
    truth: bool,
) -> Vec<ProofStep> {
    let (ra, rb) = (rat(a), rat(b));
    let dec = |name: &str, x: &Term, y: &Term| terms![name.into(), x.clone(), y.clone(), intro_top()];
    // `¬ ¬ p` from `p`.
    let not_not = |p: Term| terms!["λ h,".into(), terms!["h".into(), p]];
    let (wrapper, proof) = match (op, truth) {
        (Operator::LessEq, true) => ("eq_⊤_intro", dec("lit_le_dec", &ra, &rb)),
        (Operator::LessEq, false) => ("eq_⊥_intro", dec("lit_lt_dec", &rb, &ra)),
        (Operator::LessThan, true) => ("eq_⊤_intro", dec("lit_lt_dec", &ra, &rb)),
        (Operator::LessThan, false) => ("eq_⊥_intro", not_not(dec("lit_le_dec", &rb, &ra))),
        (Operator::GreaterEq, true) => ("eq_⊤_intro", dec("lit_le_dec", &rb, &ra)),
        (Operator::GreaterEq, false) => ("eq_⊥_intro", dec("lit_lt_dec", &ra, &rb)),
        (Operator::GreaterThan, true) => ("eq_⊤_intro", dec("lit_lt_dec", &rb, &ra)),
        (Operator::GreaterThan, false) => ("eq_⊥_intro", not_not(dec("lit_le_dec", &ra, &rb))),
        // Canonical literals: equal rationals print identically.
        (Operator::Equals, true) => ("eq_⊤_intro", terms!["eq_refl".into(), Term::Real(a.clone())]),
        (Operator::Equals, false) => ("eq_⊥_intro", dec("lit_ne_dec", &ra, &rb)),
        _ => return vec![ProofStep::Admit],
    };
    vec![ProofStep::Refine(
        terms![Term::from(wrapper), Term::Underscore, proof],
        SubProofs(None),
    )]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::translation::lambdapi::test_macros::parse_test_instance;

    /// Translate one `la_generic` step and print it.
    fn script_of(problem: &str, proof: &str) -> String {
        let (_, proof, _, mut pool) = parse_test_instance(problem, proof).unwrap();
        let mut features = Features::EMPTY;
        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            &mut pool,
            &Config::default(),
            &mut features,
            |id, t, ps| Command::Symbol(None, normalize_name(id), vec![], t, ps.map(Proof)),
        )
        .expect("translate la_generic");
        assert!(features.contains(Features::REAL), "a real la_generic reports REAL");
        assert!(!features.contains(Features::INT), "a real la_generic does not report INT");
        format!("{}", res.last().unwrap())
    }

    fn one_line(s: &str) -> String {
        s.split_whitespace().collect::<Vec<_>>().join(" ")
    }

    /// The script `alethe-lp/proofs/lra_proto.lp` checks, for two non-strict
    /// literals: the sum is `≥ᵣ`, closed by `val_lt_zero`.
    #[test]
    fn non_strict_literals_sum_to_ge() {
        let script = script_of(
            "(declare-fun x () Real)
             (declare-fun y () Real)",
            "(step t1 (cl (not (<= x y)) (not (<= y (- x 1/1)))) :rule la_generic :args (1/1 1/1))",
        );
        for expected in [
            "try rewrite (Rinv_le_eq );",
            "rewrite (R_diff_geq_zero_eq ( —ᵣ x ) ( —ᵣ y ));",
            "rewrite (Rmult_ge_compat_zero_eq (lit (Stdlib.Z.1 / Stdlib.Pos.1)) ( ( —ᵣ x ) −ᵣ ( —ᵣ y ) ) ( lit_pos Stdlib.Z.1 Stdlib.Pos.1 ⊤ᵢ ));",
            "rewrite (imp_eq_or );assume H0;assume H1;",
            "set l ≔ H0l' ＋ᵣ H1l';",
            "have sum : π (( l ≥ᵣ zero )) { refine ( Rsum0_ge_ge H0l' ( H1l' ) H0 H1 ) ; };",
            "refine ( Rge_lt_absurd l _ sum ) ;",
            "rewrite (reflect ( reify l ₁ ) ( reify l ₂ ) l ( eq_refl l ));",
            "refine ( val_lt_zero ( norm_speed ( lin ( reify l ₁ ) ) ) ( reify l ₂ ) ⊤ᵢ ) ;",
            "simplify;rewrite (or_identity_r );apply ( π̇ₗ Hla );",
        ] {
            assert!(
                one_line(&script).contains(&one_line(expected)),
                "missing `{expected}` in\n{script}"
            );
        }
        assert!(!script.contains(">_eq_≥_succ"), "step 4 is integer-only:\n{script}");
    }

    /// `poly_simp`: both sides reified in one environment, normalised with
    /// canonical coefficients, equal by conversion.
    #[test]
    fn poly_simp_reflects_both_sides_in_one_environment() {
        let script = script_of(
            "(declare-fun v1 () Real)
             (declare-fun v2 () Real)",
            "(step t1 (cl (= (- v1 v2) (+ v1 (* -1/1 v2)))) :rule poly_simp)",
        );
        for expected in [
            "apply ∨ᵢ₁;",
            "set env ≔ ( rfy ( reify ( v1 −ᵣ v2 ) ₂ ) ( v1 ＋ᵣ ( (lit (Stdlib.Z.-1 / Stdlib.Pos.1)) *ᵣ v2 ) ) ₂ );",
            "refine ( eq_trans ( v1 −ᵣ v2 ) _ ( v1 ＋ᵣ ( (lit (Stdlib.Z.-1 / Stdlib.Pos.1)) *ᵣ v2 ) ) ( reflect_canon ( rfy env ( v1 −ᵣ v2 ) ₁ ) env ( v1 −ᵣ v2 ) ( eq_refl ( v1 −ᵣ v2 ) ) )",
            "( eq_sym ( reflect_canon ( rfy env ( v1 ＋ᵣ",
        ] {
            assert!(one_line(&script).contains(&one_line(expected)), "missing `{expected}` in\n{script}");
        }
    }

    /// `poly_simp_rel`: the lemma is chosen by the relation and the signs of
    /// the coefficients; `=` takes any non-zero ones.
    #[test]
    fn poly_simp_rel_picks_the_lemma_by_relation_and_sign() {
        let script = script_of(
            "(declare-fun p () Real)
             (declare-fun v1 () Real)
             (declare-fun q () Real)",
            "(step t1 (cl (= (* -1/1 (- 1/1 p)) (* 1/1 (- v1 q)))) :rule poly_simp)
             (step t2 (cl (= (= 1/1 p) (= v1 q))) :rule poly_simp_rel :premises (t1))",
        );
        assert!(
            one_line(&script).contains(&one_line(
                "refine ( poly_rel_eq (lit (Stdlib.Z.-1 / Stdlib.Pos.1)) (lit (Stdlib.Z.1 / Stdlib.Pos.1)) p (lit (Stdlib.Z.1 / Stdlib.Pos.1)) v1 q ( lit_ne_zero Stdlib.Z.-1 Stdlib.Pos.1 ⊤ᵢ ) ( lit_ne_zero Stdlib.Z.1 Stdlib.Pos.1 ⊤ᵢ ) ( π̇ₗ t1 ) ) ;"
            )),
            "{script}"
        );
        let script = script_of(
            "(declare-fun x () Real)
             (declare-fun y () Real)",
            "(step t1 (cl (= (* -1/1 (- x y)) (* -3/2 (- y x)))) :rule poly_simp)
             (step t2 (cl (= (< x y) (< y x))) :rule poly_simp_rel :premises (t1))",
        );
        assert!(
            one_line(&script).contains(&one_line(
                "poly_rel_lt_neg (lit (Stdlib.Z.-1 / Stdlib.Pos.1)) x y (lit (Stdlib.Z.-3 / Stdlib.Pos.2)) y x ( lit_neg_lt_zero Stdlib.Pos.1 Stdlib.Pos.1 ) ( lit_neg_lt_zero Stdlib.Pos.3 Stdlib.Pos.2 )"
            )),
            "{script}"
        );
    }

    /// `evaluate`: a comparison of numerals is decided on `b 𝕢- a`, an
    /// equality goes through the reflection, the Boolean case is `¬⊤`.
    #[test]
    fn evaluate_decides_comparisons_and_folds_equalities() {
        let script = script_of(
            "(declare-fun a () Real)",
            "(step t1 (cl (= (>= 0/1 -1/1) true)) :rule evaluate)",
        );
        assert!(
            one_line(&script).contains(&one_line(
                "apply ∨ᵢ₁;refine ( eq_⊤_intro _ ( lit_le_dec ( Stdlib.Z.-1 / Stdlib.Pos.1 ) ( Stdlib.Z.0 / Stdlib.Pos.1 ) ⊤ᵢ ) ) ;"
            )),
            "{script}"
        );
        let script = script_of(
            "(declare-fun a () Real)",
            "(step t1 (cl (= (< 1/1 0/1) false)) :rule evaluate)",
        );
        assert!(
            one_line(&script).contains(&one_line(
                "refine ( eq_⊥_intro _ ( λ h, ( h ( lit_le_dec ( Stdlib.Z.0 / Stdlib.Pos.1 ) ( Stdlib.Z.1 / Stdlib.Pos.1 ) ⊤ᵢ ) ) ) ) ;"
            )),
            "{script}"
        );
        let script = script_of(
            "(declare-fun a () Real)",
            "(step t1 (cl (= (* 1/1 0/1) 0/1)) :rule evaluate)",
        );
        assert!(one_line(&script).contains("reflect_canon"), "{script}");
        assert!(!script.contains("admit"), "{script}");
    }

    /// `unsat-11-arith`'s shape: a strict literal, an equality with a negative
    /// coefficient, and a positive literal. The sum is `>ᵣ`, closed by
    /// `val_le_zero`; the equality is scaled with its sign and weakened.
    #[test]
    fn a_strict_literal_makes_the_sum_strict() {
        let script = script_of(
            "(declare-fun f (Real) Real)",
            "(step t1 (cl (not (< (f 5/1) 5/1))
                          (not (= (* -1/1 (f 5/1)) (* -1/1 12/1)))
                          (< (+ (f 5/1) (* -1/1 (f 5/1))) (+ 5/1 (* -1/1 12/1))))
                 :rule la_generic :args (1/1 -1/1 1/1))",
        );
        for expected in [
            "rewrite .[x in _ ∨ _ ∨ x] (Rlt_not_ge );",
            "try rewrite (Rinv_lt_eq );",
            "R_diff_gt_zero_eq",
            "R_diff_eq_zero_eq",
            "R_diff_geq_zero_eq",
            "Rmult_gt_compat_zero_eq (lit (Stdlib.Z.1 / Stdlib.Pos.1))",
            "Rmult_eq_compat_zero_eq (lit (Stdlib.Z.-1 / Stdlib.Pos.1))",
            "( lit_ne_zero Stdlib.Z.-1 Stdlib.Pos.1 ⊤ᵢ )",
            "rewrite (imp_eq_or );assume H0;rewrite (imp_eq_or );assume H1;assume H2;",
            "have sum : π (( l >ᵣ zero )) { refine ( Rsum0_gt_ge H0l' ( H1l' ＋ᵣ H2l' ) H0 ( Rsum0_ge_ge H1l' ( H2l' ) ( R_eq_ge H1l' H1 ) H2 ) ) ; };",
            "refine ( Rgt_le_absurd l _ sum ) ;",
            "refine ( val_le_zero",
        ] {
            assert!(
                one_line(&script).contains(&one_line(expected)),
                "missing `{expected}` in\n{script}"
            );
        }
    }
}
