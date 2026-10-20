//! Linear integer arithmetic: `la_generic` and the `la_*` rules. Mirrors
//! `alethe-lp/lia.lp`; the arithmetic RARE rewrites are in `rare/lia.rs`.

use rug::{Integer, Rational};
use crate::translation::lambdapi::*;
use crate::ast::{Operator, Rc, Term as AletheTerm, match_term, match_term_err};

/// `la_generic`: the clause is a tautology because the linear combination of
/// its negated literals, with the step's `:args` as coefficients, is a
/// contradictory constant. The coefficients are the certificate, so the whole
/// step is one `refine` of `lia.lp`'s reflective checker:
///
/// ```text
/// refine (Zla_generic (a₁ ⸬ … ⸬ □) (φ₁ ⸬ … ⸬ □) ⊤ᵢ);
/// ```
///
/// `Zla_generic` reifies the clause, `check`s the certificate by computation
/// (`⊤ᵢ` discharges it) and its type is the clause itself by conversion.
/// Rational coefficients are scaled by the lcm of their denominators first:
/// a Farkas certificate is invariant under scaling, and over ℤ the checker
/// takes integers.
pub fn gen_proof_la_generic(
    clause: &[Rc<AletheTerm>],
    args: &[Rc<AletheTerm>],
    ctx: &Context,
) -> Vec<ProofStep> {
    let coefficients = Term::Alethe(LTerm::List(List(
        integer_coefficients(args).into_iter().map(Term::Int).collect(),
    )));
    // The clause with the shared `p_N` names, like the step's own type.
    let clause = Term::Terms(vec![Term::Alethe(LTerm::Clauses(
        clause.iter().map(|t| ctx.get_or_convert(t).0).collect(),
    ))]);
    vec![ProofStep::Refine(
        terms![Term::from("Zla_generic"), coefficients, clause, intro_top()],
        SubProofs(None),
    )]
}

/// The step's coefficients, scaled by the lcm of their denominators.
fn integer_coefficients(args: &[Rc<AletheTerm>]) -> Vec<Integer> {
    let coefficients = super::lra::coefficients(args);
    let lcm = coefficients
        .iter()
        .fold(Integer::from(1), |acc, c| acc.lcm(c.denom()));
    coefficients
        .into_iter()
        .map(|c| {
            let scaled = c * &lcm;
            debug_assert!(scaled.is_integer());
            scaled.numer().clone()
        })
        .collect()
}

/// `poly_simp`: `(= t s)` for `t` and `s` the same polynomial over ℤ. The
/// RARE `arith-poly-norm` script, reached by its Alethe name.
pub fn translate_poly_simp(clause: &[Rc<AletheTerm>]) -> TradResult<Proof> {
    match_term!((= l r) = clause[0]).ok_or(TranslatorError::PremisesError)?;
    let mut proof = vec![ProofStep::Apply(Term::from("∨ᵢ₁"), SubProofs(None))];
    proof.extend(poly_norm_steps());
    Ok(Proof(proof))
}

pub(crate) use super::rare::lia::poly_norm_steps;

/// A numeral as a ℤ literal, if it is one.
fn int_literal_of(r: &Rational) -> Option<Term> {
    (*r.denom() == 1).then(|| Term::Int(r.numer().clone()))
}

/// `poly_simp_rel`: from `c₁·(x₁ − x₂) = c₂·(y₁ − y₂)`, the relations
/// `x₁ ⋈ x₂` and `y₁ ⋈ y₂` are the same proposition: `lia.lp`'s
/// `Zpoly_rel_<rel>_pos` for positive coefficients, `Zpoly_rel_eq` for `=`
/// with any non-zero ones. Their side conditions compute to ⊤ on numerals.
/// Negative coefficients on an inequality are not covered over ℤ.
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
    let lemma = match op {
        Operator::Equals => "Zpoly_rel_eq",
        _ if !(c1.is_positive() && c2.is_positive()) => return Err(unsupported()),
        Operator::LessEq => "Zpoly_rel_le_pos",
        Operator::LessThan => "Zpoly_rel_lt_pos",
        Operator::GreaterEq => "Zpoly_rel_ge_pos",
        Operator::GreaterThan => "Zpoly_rel_gt_pos",
        _ => return Err(unsupported()),
    };
    let (c1, c2) = (
        int_literal_of(&c1).ok_or_else(unsupported)?,
        int_literal_of(&c2).ok_or_else(unsupported)?,
    );
    Ok(Proof(vec![
        ProofStep::Apply(Term::from("∨ᵢ₁"), SubProofs(None)),
        ProofStep::Refine(
            terms![
                Term::from(lemma),
                c1,
                Term::from(x1),
                Term::from(x2),
                c2,
                Term::from(y1),
                Term::from(y2),
                intro_top(),
                intro_top(),
                unary_clause_to_prf(&premise.0)
            ],
            SubProofs(None),
        ),
    ]))
}

/// `evaluate` on a comparison of two ℤ numerals, `(= (a ⋈ b) true|false)`:
/// `lia.lp`'s `Z<rel>_<truth> a b`, whose `istrue` hypothesis computes to ⊤.
pub(crate) fn evaluate_comparison(
    op: Operator,
    a: &Rational,
    b: &Rational,
    truth: bool,
) -> Vec<ProofStep> {
    let (Some(a), Some(b)) = (int_literal_of(a), int_literal_of(b)) else {
        return vec![ProofStep::Admit];
    };
    let rel = match op {
        Operator::Equals => "eq",
        Operator::LessThan => "lt",
        Operator::LessEq => "le",
        Operator::GreaterThan => "gt",
        Operator::GreaterEq => "ge",
        _ => return vec![ProofStep::Admit],
    };
    let lemma = format!("Z{rel}_{}", if truth { "true" } else { "false" });
    vec![ProofStep::Refine(
        terms![Term::from(lemma), a, b, intro_top()],
        SubProofs(None),
    )]
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::translation::lambdapi::test_macros::parse_test_instance;

    /// Translate one step over the integers and print it.
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
        .expect("translate the step");
        assert!(features.contains(Features::INT), "an integer step reports INT");
        assert!(!features.contains(Features::REAL), "an integer step does not report REAL");
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
            "(declare-fun n () Int)
             (declare-fun m () Int)",
            "(step t1 (cl (not (<= n m)) (<= n m)) :rule la_generic :args (1 1))",
        );
        let script = one_line(&script);
        assert!(
            script.contains("refine ( Zla_generic (Stdlib.Z.1 ⸬ Stdlib.Z.1 ⸬ □) ( ((¬ ( n ≤ m ))) ⸬ (( n ≤ m )) ⸬ □ ) ⊤ᵢ ) ;"),
            "unexpected script:\n{script}"
        );
        for old in ["rewrite", "assume", "set ", "have ", "reify_correct"] {
            assert!(!script.contains(old), "the per-literal script is gone:\n{script}");
        }
    }

    /// cvc5 prints `1/1`; a genuine fraction is scaled away with the others.
    #[test]
    fn rational_coefficients_are_scaled_to_integers() {
        let script = script_of(
            "(declare-fun n () Int)",
            "(step t1 (cl (not (<= n 0)) (not (<= 1 (* 2 n)))) :rule la_generic :args (1/1 1/2))",
        );
        assert!(
            one_line(&script).contains("Zla_generic (Stdlib.Z.2 ⸬ Stdlib.Z.1 ⸬ □)"),
            "unexpected script:\n{script}"
        );
    }

    /// A negative coefficient keeps its sign: the checker takes |a| itself for
    /// an inequality and the signed a for an equality.
    #[test]
    fn negative_coefficients_keep_their_sign() {
        let script = script_of(
            "(declare-fun n () Int)
             (declare-fun m () Int)",
            "(step t1 (cl (not (= n m)) (not (<= n m))) :rule la_generic :args ((- 1) 1))",
        );
        assert!(
            one_line(&script).contains("Zla_generic (Stdlib.Z.-1 ⸬ Stdlib.Z.1 ⸬ □)"),
            "unexpected script:\n{script}"
        );
    }
}
