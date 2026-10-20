//! Linear real arithmetic: `la_generic` over the reals, `poly_simp` and
//! `evaluate`. Mirrors `alethe-lp/lra.lp`. The arithmetic RARE rewrites over
//! the reals are the `RareLra` entries of `rare/mod.rs`, and
//! `la_disequality`/`la_totality` reuse the `lia.rs` scripts, since `lra.lp`
//! declares those lemmas under the same names.

use crate::ast::{Constant, Operator, Rc, Term as AletheTerm, match_term};
use crate::translation::lambdapi::*;
use rug::Rational;

/// `la_generic` over the reals: one `refine` of `lra.lp`'s reflective checker,
/// as `lia::gen_proof_la_generic` does over ℤ, with the coefficients kept
/// rational (`n / d`, as `alethe.rat` writes them).
///
/// ```text
/// refine (Rla_generic (a₁ ⸬ … ⸬ □) (φ₁ ⸬ … ⸬ □) ⊤ᵢ);
/// ```
pub fn gen_proof_la_generic(
    clause: &[Rc<AletheTerm>],
    args: &[Rc<AletheTerm>],
    ctx: &Context,
) -> Vec<ProofStep> {
    let coefficients = Term::Alethe(LTerm::List(List(
        coefficients(args).iter().map(rat).collect(),
    )));
    let clause = Term::Terms(vec![Term::Alethe(LTerm::Clauses(
        clause.iter().map(|t| ctx.get_or_convert(t).0).collect(),
    ))]);
    vec![ProofStep::Refine(
        terms![Term::from("Rla_generic"), coefficients, clause, intro_top()],
        SubProofs(None),
    )]
}

/// The step's `:args`, one coefficient per literal: a numeral, possibly negated.
pub(super) fn coefficients(args: &[Rc<AletheTerm>]) -> Vec<Rational> {
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

    /// The whole step is one `refine` of the reflective checker, on the clause
    /// itself and the step's coefficients.
    #[test]
    fn la_generic_is_one_refine_of_the_checker() {
        let script = script_of(
            "(declare-fun x () Real)
             (declare-fun y () Real)",
            "(step t1 (cl (not (<= x y)) (not (<= y (- x 1/1)))) :rule la_generic :args (1/1 1/1))",
        );
        let script = one_line(&script);
        assert!(
            script.contains("refine ( Rla_generic (( Stdlib.Z.1 / Stdlib.Pos.1 ) ⸬ ( Stdlib.Z.1 / Stdlib.Pos.1 ) ⸬ □) ( ((¬ ( x ≤ᵣ y ))) ⸬ ((¬ ( y ≤ᵣ ( x −ᵣ (lit (Stdlib.Z.1 / Stdlib.Pos.1)) ) ))) ⸬ □ ) ⊤ᵢ ) ;"),
            "unexpected script:\n{script}"
        );
        for old in ["rewrite", "assume", "set ", "have ", "reflect"] {
            assert!(!script.contains(old), "the per-literal script is gone:\n{script}");
        }
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
    /// coefficient, and a positive literal. The coefficients keep their sign and
    /// denominator: the checker takes |a| itself for an inequality.
    #[test]
    fn coefficients_keep_their_sign_and_denominator() {
        let script = script_of(
            "(declare-fun f (Real) Real)",
            "(step t1 (cl (not (< (f 5/1) 5/1))
                          (not (= (* -1/1 (f 5/1)) (* -1/1 12/1)))
                          (< (+ (f 5/1) (* -1/1 (f 5/1))) (+ 5/1 (* -1/1 12/1))))
                 :rule la_generic :args (1/1 -1/2 1/1))",
        );
        assert!(
            one_line(&script).contains("Rla_generic (( Stdlib.Z.1 / Stdlib.Pos.1 ) ⸬ ( Stdlib.Z.-1 / Stdlib.Pos.2 ) ⸬ ( Stdlib.Z.1 / Stdlib.Pos.1 ) ⸬ □)"),
            "unexpected script:\n{script}"
        );
    }
}
