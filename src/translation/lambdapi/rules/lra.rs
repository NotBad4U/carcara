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
use crate::ast::{Constant, Operator, Rc, Term as AletheTerm};
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
