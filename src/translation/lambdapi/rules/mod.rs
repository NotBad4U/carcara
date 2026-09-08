//! One Rust module per Lambdapi library module: every Alethe rule is
//! dispatched to exactly one of them.

pub mod core;
pub mod lia;
pub mod prop;
pub mod quant;

pub use core::*;
pub use lia::*;
pub use prop::*;
pub use quant::*;

use crate::translation::lambdapi::logic::Features;
use crate::translation::lambdapi::*;
use crate::ast::{Rc, Term as AletheTerm};

pub fn translate_simple_tautology(
    rule: &str,
    premises: &[(String, &[Rc<AletheTerm>])],
) -> TradResult<Proof> {
    Ok(Proof(vec![ProofStep::Apply(
        terms![
            Term::TermId(rule.to_owned()),
            ..premises
                .iter()
                .map(|(name, _)| Term::TermId(name.clone()))
                .collect_vec()
        ],
        SubProofs(None),
    )]))
}

/// Corresponding to the symbol application π̇ₗ x,
/// where π̇ₗ: π̇ (a ⸬ □)  → π a
pub(crate) fn unary_clause_to_prf(premise_id: &str) -> Term {
    Term::Terms(vec![Term::from("π̇ₗ"), Term::from(premise_id)])
}

pub(crate) fn get_premises_clause<'a>(
    proof_iter: &'a ProofIter,
    premises: &'a [(usize, usize)],
) -> Vec<(String, &'a [Rc<AletheTerm>])> {
    premises
        .iter()
        .map(|p| proof_iter.get_premise(*p))
        .map(|c| (normalize_name(c.id()), c.clause()))
        .collect_vec()
}

/// Alethe rules proved by a library lemma of the same name: the whole script is
/// `apply <rule> <premises>`. Derived from the library — every name here is
/// checked against `alethe-lp/*.lp` by `lemma_rules_exist`.
const LEMMA_RULES: &[&str] = &[
    "distinct_elim",
    "equiv1",
    "equiv2",
    "equiv_neg1",
    "equiv_neg2",
    "equiv_pos1",
    "equiv_pos2",
    "implies_neg1",
    "implies_neg2",
    "implies_pos",
    "ite_neg1",
    "ite_neg2",
    "ite_pos1",
    "ite_pos2",
    "not_ite1",
    "not_ite2",
    "not_not",
    "xor_neg1",
    "xor_neg2",
    "xor_pos1",
    "xor_pos2",
];

/// Rules the backend knowingly leaves unproved: it emits `admit` so the rest of
/// the proof still checks. Kept explicit so the gap is visible rather than
/// hidden behind a catch-all.
const ADMITTED_RULES: &[(&str, Features)] = &[
    ("all_simplify", Features::EMPTY),
    ("bool_simplify", Features::EMPTY),
    ("comp_simplify", Features::INT),
    ("connective_def", Features::EMPTY),
    ("evaluate", Features::EMPTY),
    ("hole", Features::EMPTY),
    ("la_mult_neg", Features::INT),
    ("la_mult_pos", Features::INT),
    ("or_pos", Features::EMPTY),
    ("reordering", Features::EMPTY),
];

/// Translate one proof step. This is the single dispatch point: every Alethe
/// rule is either matched here, listed in [`LEMMA_RULES`] or [`ADMITTED_RULES`],
/// or reported as [`TranslatorError::UnsupportedRule`].
///
/// Returns the proof script (`None` when the step is emitted by the enclosing
/// subproof instead) together with the theory features the script needs.
pub fn translate_step(
    ctx: &mut Context,
    proof_iter: &mut ProofIter<'_>,
    pool: &mut PrimitivePool,
    clause: &[Rc<AletheTerm>],
    premises: &[(usize, usize)],
    rule: &str,
    args: &[Rc<AletheTerm>],
    config: &Config,
) -> TradResult<(Option<Vec<ProofStep>>, Features)> {
    use Features as F;

    let steps = |p: Proof| Ok((Some(p.0), F::EMPTY));
    let with = |p: Proof, f: Features| Ok((Some(p.0), f));

    // `?` on a missing premise used to silently drop the step; make it explicit.
    let mut prems = get_premises_clause(proof_iter, premises);
    let first = |p: &Vec<(String, &[Rc<AletheTerm>])>| -> TradResult<String> {
        p.first()
            .map(|(n, _)| n.clone())
            .ok_or(TranslatorError::PremisesError)
    };

    match rule {
        // Emitted by the enclosing ProofCommand::Subproof arm.
        "bind" | "subproof" => Ok((None, F::EMPTY)),

        "resolution" | "th_resolution" => Ok((
            Some(self::core::translate_resolution(proof_iter, premises, args, ctx, pool)),
            F::EMPTY,
        )),

        "rare_rewrite" => {
            let dag_terms = clause
                .iter()
                .flat_map(|a| ctx.get_or_convert(a).1)
                .collect();
            // The RARE rule name is emitted verbatim as the lemma to apply. Most
            // live in `prop.lp`, but the `arith-*` family is declared in `lia.lp`,
            // so those pull in the integer layer.
            let feature = match args.first().map(|a| format!("{}", a)) {
                Some(name) if name.trim_matches('"').starts_with("arith-") => F::INT,
                _ => F::EMPTY,
            };
            with(self::prop::translate_rare_simp(clause, args, dag_terms), feature)
        }

        "la_generic" => Ok((Some(self::lia::gen_proof_la_generic(clause, args, pool)), F::INT)),

        // ---- core: equality, congruence and the clause level ---------------
        "refl" => steps(self::core::translate_refl()?),
        "symm" => steps(self::core::translate_sym(first(&prems)?.as_str())?),
        "not_symm" => steps(self::core::translate_not_symm(first(&prems)?.as_str())?),
        "trans" => steps(self::core::translate_trans(&mut prems)?),
        "cong" => steps(self::core::translate_cong(clause, prems.as_slice())?),
        "contraction" => {
            let p = prems.first().ok_or(TranslatorError::PremisesError)?;
            steps(self::core::translate_contraction(clause, p)?)
        }

        // ---- prop: propositional tautologies and Boolean rewrites ----------
        "true" => steps(self::prop::translate_true()?),
        "false" => steps(self::prop::translate_false()?),
        "and_neg" => steps(self::prop::translate_and_neg(clause)?),
        "and_pos" => steps(self::prop::translate_and_pos(clause, args)?),
        "or_neg" => steps(self::prop::translate_or_neg(clause, args)?),
        "not_and" => steps(self::prop::translate_not_and(clause, first(&prems)?.as_str())?),
        "not_or" => {
            let p = prems.first().ok_or(TranslatorError::PremisesError)?;
            steps(self::prop::translate_not_or(p, args)?)
        }
        "nary_elim" => steps(self::prop::translate_nary_elim()?),
        "implies" => steps(self::prop::translate_implies(first(&prems)?.as_str())?),
        "not_implies1" => steps(self::prop::translate_not_implies1(first(&prems)?.as_str())?),
        "not_implies2" => steps(self::prop::translate_not_implies2(first(&prems)?.as_str())?),
        "and" => {
            let p = prems.first().ok_or(TranslatorError::PremisesError)?;
            steps(self::prop::translate_and(p, args)?)
        }
        "and_intro" => steps(self::prop::translate_and_intro(prems.as_slice())?),
        "or" => {
            let p = prems.first().ok_or(TranslatorError::PremisesError)?;
            steps(self::prop::translate_or(p)?)
        }
        "ite1" => {
            let p = prems.first().ok_or(TranslatorError::PremisesError)?;
            steps(self::prop::translate_ite1(p)?)
        }
        "ite2" => {
            let p = prems.first().ok_or(TranslatorError::PremisesError)?;
            steps(self::prop::translate_ite2(p)?)
        }
        "equiv_simplify" | "not_simplify" | "implies_simplify" | "ite_simplify" | "ac_simp" => {
            steps(self::prop::translate_simplify_step(rule).ok_or_else(|| {
                TranslatorError::UnsupportedRule(rule.to_owned())
            })?)
        }

        // ---- quant --------------------------------------------------------
        "forall_inst" => with(self::quant::translate_forall_inst(args)?, F::QUANT),
        "sko_forall" => with(self::quant::translate_sko_forall()?, F::QUANT),

        // ---- lia ----------------------------------------------------------
        "la_disequality" => with(self::lia::translate_la_disequality(clause)?, F::INT),

        // Declared in `lia.lp` like `la_disequality`, so it must report INT too.
        // It used to sit in `LEMMA_RULES`, whose fall-through reports `F::EMPTY` --
        // harmless while `alethe.lia` was opened unconditionally, an unbound symbol
        // once the header is gated on the feature.
        "la_totality" => with(translate_simple_tautology(rule, prems.as_slice())?, F::INT),

        _ => {
            if let Some((_, f)) = ADMITTED_RULES.iter().find(|(n, _)| *n == rule) {
                return Ok((Some(admit()), *f));
            }
            if LEMMA_RULES.contains(&rule) {
                return steps(translate_simple_tautology(rule, prems.as_slice())?);
            }
            if config.admit_unsupported {
                return Ok((Some(admit()), F::EMPTY));
            }
            Err(TranslatorError::UnsupportedRule(rule.to_owned()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every rule routed through the catch-all must name a symbol that really
    /// exists in the library, otherwise the generated proof gets an unbound
    /// identifier that only surfaces at `lambdapi check` time.
    #[test]
    fn lemma_rules_exist_in_the_library() {
        let mut sources = String::new();
        for m in ["core", "prop", "quant", "lia"] {
            sources += &std::fs::read_to_string(format!("alethe-lp/{m}.lp"))
                .unwrap_or_else(|e| panic!("cannot read {m}.lp: {e}"));
        }
        let declared: Vec<&str> = sources
            .lines()
            .filter_map(|l| l.split_once("symbol "))
            .map(|(_, rest)| rest.split([' ', ':', '[', '(']).next().unwrap_or(""))
            .collect();
        for rule in LEMMA_RULES {
            assert!(
                declared.contains(rule),
                "rule `{rule}` is dispatched to the catch-all `apply {rule}`, \
                 but no such symbol is declared in the library"
            );
        }
    }
}
