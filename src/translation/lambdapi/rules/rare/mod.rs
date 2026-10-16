//! The cvc5 RARE rewrites. Each reaches the translator as a `rare_rewrite` step
//! whose first argument names the rule, and [`RARE_RULES`] maps that name to a
//! proof. Mirrors `alethe-lp/rare/`: one Rust module per library module, holding
//! the scripts of the rules that need more than an `apply` of their lemma.
//!
//! `evaluate` and `arith-poly-norm` arrive through the same step but are cvc5
//! rewrites without a RARE definition; they are registered here all the same.

pub mod lia;
pub mod prop;

use crate::ast::{Constant, Operator, Rc, Term as AletheTerm, match_term};
use crate::translation::lambdapi::library::Module;
use crate::translation::lambdapi::rules::bv;
use crate::translation::lambdapi::*;
use crate::translation::lambdapi::logic::Features;

/// What a script for a RARE rule gets to see of its step.
pub struct RareStep<'a> {
    pub clause: &'a [Rc<AletheTerm>],
    /// The rule's arguments, without the rule name.
    pub args: &'a [Rc<AletheTerm>],
    /// The step's premises: the conditions of a `define-cond-rule`, in order.
    pub premises: &'a [(String, &'a [Rc<AletheTerm>])],
    /// The arithmetic carrier the step is about, if any: `evaluate` folds
    /// over ℤ and over ℝ with different scripts.
    pub carrier: Option<Features>,
}

/// How the backend proves a RARE rule.
#[derive(Clone, Copy)]
pub enum Rare {
    /// `apply` the library lemma named after the rule to the step's arguments,
    /// then to its premises. A `define-cond-rule` lemma takes its conditions as
    /// hypotheses after its variables.
    Lemma,
    /// [`Rare::Lemma`] whose integer constant arguments are widths or indices
    /// of bit-vector operators -- `(zero_extend n x)` -- and so are printed as
    /// `Stdlib.Nat.n`, the ℕ the `alethe.bv` lemma takes, not as `Stdlib.Z.n`.
    NatLemma,
    /// A script built from the step.
    Script(fn(&RareStep<'_>) -> Vec<ProofStep>),
}

/// Every RARE rule the backend proves, with the module its proof cites. A
/// `rare_rewrite` step naming any other rule is unsupported.
///
/// A `Lemma` must be declared in its module. A script's module is the widest one
/// it may cite: the Boolean scripts fall back on their lemma or on `core`'s
/// identities depending on the arguments.
pub const RARE_RULES: &[(&str, Module, Rare)] = {
    use Module::{Core, Lia, RareBv, RareLia, RareLra, RareProp, Tauto};
    use Rare::{Lemma, NatLemma, Script};
    &[
        // ---- alethe-lp/rare/prop.lp ------------------------------------------
        ("bool-and-conf", RareProp, Script(prop::translate_bool_and_conf)),
        ("bool-and-conf2", RareProp, Script(prop::translate_bool_and_conf2)),
        ("bool-and-de-morgan", RareProp, Script(prop::translate_bool_and_de_morgan)),
        ("bool-and-false", RareProp, Lemma),
        ("bool-and-flatten", RareProp, Script(prop::translate_bool_and_flatten)),
        ("bool-and-true", RareProp, Script(prop::translate_bool_and_true)),
        ("bool-double-not-elim", RareProp, Script(prop::translate_bool_double_not_elim)),
        ("bool-dual-impl-eq", RareProp, Lemma),
        ("bool-eq-false", RareProp, Script(prop::translate_bool_eq_false)),
        ("bool-eq-nrefl", RareProp, Lemma),
        ("bool-eq-true", RareProp, Script(prop::translate_bool_eq_true)),
        ("bool-impl-elim", RareProp, Script(prop::translate_bool_impl_elim)),
        ("bool-impl-false1", RareProp, Script(prop::translate_bool_imp_false1)),
        ("bool-impl-false2", RareProp, Script(prop::translate_bool_imp_false2)),
        ("bool-impl-true1", RareProp, Script(prop::translate_bool_imp_true1)),
        ("bool-impl-true2", RareProp, Script(prop::translate_bool_imp_true2)),
        ("bool-implies-de-morgan", RareProp, Lemma),
        ("bool-implies-or-distrib", RareProp, Script(prop::translate_bool_implies_or_distrib)),
        ("bool-not-eq-elim1", RareProp, Lemma),
        ("bool-not-eq-elim2", RareProp, Lemma),
        ("bool-not-false", RareProp, Lemma),
        ("bool-not-ite-elim", RareProp, Lemma),
        ("bool-not-true", RareProp, Lemma),
        ("bool-not-xor-elim", RareProp, Lemma),
        ("bool-or-and-distrib", RareProp, Script(prop::translate_bool_or_and_distrib)),
        ("bool-or-de-morgan", RareProp, Script(prop::translate_bool_or_de_morgan)),
        ("bool-or-false", RareProp, Script(prop::translate_bool_or_false)),
        ("bool-or-flatten", RareProp, Script(prop::translate_bool_or_flatten)),
        ("bool-or-taut", RareProp, Script(prop::translate_bool_or_taut)),
        ("bool-or-taut2", RareProp, Script(prop::translate_bool_or_taut2)),
        ("bool-xor-comm", RareProp, Lemma),
        ("bool-xor-elim", RareProp, Lemma),
        ("bool-xor-false", RareProp, Lemma),
        ("bool-xor-nrefl", RareProp, Lemma),
        ("bool-xor-refl", RareProp, Lemma),
        ("bool-xor-true", RareProp, Lemma),
        ("distinct-binary-elim", RareProp, Lemma),
        ("eq-refl", RareProp, Lemma),
        ("eq-symm", RareProp, Lemma),
        ("ite-else-false", RareProp, Lemma),
        ("ite-else-lookahead-not-self", RareProp, Lemma),
        ("ite-else-lookahead-self", RareProp, Lemma),
        ("ite-else-true", RareProp, Lemma),
        ("ite-eq", RareProp, Lemma),
        ("ite-expand", RareProp, Lemma),
        ("ite-neg-branch", RareProp, Lemma),
        ("ite-then-false", RareProp, Lemma),
        ("ite-then-lookahead-not-self", RareProp, Lemma),
        ("ite-then-lookahead-self", RareProp, Lemma),
        ("ite-then-true", RareProp, Lemma),
        // Proved by `simplify; reflexivity` or admitted: no library lemma.
        ("evaluate", Core, Script(translate_evaluate)),
        // `t = t` is `⊤`, after which the step is propositional: `#cauto`.
        ("or-not-refl", Tauto, Script(prop::translate_or_not_refl)),
        // ---- alethe-lp/rare/lia.lp -------------------------------------------
        ("arith-elim-gt", RareLia, Lemma),
        ("arith-elim-leq", RareLia, Lemma),
        ("arith-elim-lt", RareLia, Lemma),
        ("arith-geq-norm1", RareLia, Lemma),
        ("arith-geq-norm2", RareLia, Lemma),
        ("arith-geq-tighten", RareLia, Lemma),
        ("arith-int-eq-elim", RareLia, Lemma),
        ("arith-leq-norm", RareLia, Lemma),
        ("arith-refl-geq", RareLia, Lemma),
        ("arith-refl-gt", RareLia, Lemma),
        ("arith-refl-leq", RareLia, Lemma),
        ("arith-refl-lt", RareLia, Lemma),
        // Reuses `la_generic`'s reification in `lia.lp`, not a RARE lemma.
        ("arith-poly-norm", Lia, Script(lia::translate_arith_poly_norm)),
        // ---- alethe-lp/rare/lra.lp -------------------------------------------
        // Its other lemmas share their rule's name with rare/lia.lp and are
        // registered there, under `RareLia`; `lookup_in` re-routes them to
        // `RareLra` for a real-sorted step (see `REAL_RARE_LEMMAS`).
        ("arith-real-eq-elim", RareLra, Lemma),
        // ---- alethe-lp/rare/bv.lp --------------------------------------------
        // `(zero_extend n x) = (concat (@bv 0 n) x)`; the step's arguments are
        // `x n`, in the order the RARE rule declares them.
        ("bv-zero-extend-eliminate", RareBv, NatLemma),
        // The structural rewrites, proved bit by bit from the conclusion (the
        // step's own arguments are partial: `bv-concat-extract-merge` arrives
        // with 3 of its 7). Each may fall back on `#cauto` for a bit, hence
        // the Tauto module; `rules::bv::translate_by_bits` reads nothing else.
        ("bv-concat-extract-merge", Tauto, Script(bv::translate_by_bits)),
        ("bv-extract-concat-1", Tauto, Script(bv::translate_by_bits)),
        ("bv-extract-concat-2", Tauto, Script(bv::translate_by_bits)),
        ("bv-extract-concat-3", Tauto, Script(bv::translate_by_bits)),
        ("bv-extract-concat-4", Tauto, Script(bv::translate_by_bits)),
        ("bv-extract-whole", Tauto, Script(bv::translate_by_bits)),
        ("bv-extract-extract", Tauto, Script(bv::translate_by_bits)),
        ("bv-concat-merge-const", Tauto, Script(bv::translate_by_bits)),
        ("bv-or-concat-pullup", Tauto, Script(bv::translate_by_bits)),
        ("bv-or-concat-pullup2", Tauto, Script(bv::translate_by_bits)),
        ("bv-and-concat-pullup", Tauto, Script(bv::translate_by_bits)),
        ("bv-and-concat-pullup2", Tauto, Script(bv::translate_by_bits)),
        ("bv-xor-concat-pullup", Tauto, Script(bv::translate_by_bits)),
        ("bv-xor-concat-pullup2", Tauto, Script(bv::translate_by_bits)),
        ("bv-extract-bitwise-and", Tauto, Script(bv::translate_by_bits)),
        ("bv-extract-bitwise-or", Tauto, Script(bv::translate_by_bits)),
        ("bv-extract-bitwise-xor", Tauto, Script(bv::translate_by_bits)),
        ("bv-extract-not", Tauto, Script(bv::translate_by_bits)),
        ("bv-concat-flatten", Tauto, Script(bv::translate_by_bits)),
    ]
};

/// The rule a `rare_rewrite` step names in its first argument.
pub fn rule_name(args: &[Rc<AletheTerm>]) -> Option<&str> {
    match &**args.first()? {
        AletheTerm::Const(Constant::String(name)) => Some(name),
        _ => None,
    }
}

/// The module and proof of a RARE rule, or `None` if the backend has none.
pub fn lookup(name: &str) -> Option<(Module, Rare)> {
    RARE_RULES
        .iter()
        .find(|(n, ..)| *n == name)
        .map(|&(_, module, how)| (module, how))
}

/// The lemmas `rare/lra.lp` proves over the reals under the same name as
/// `rare/lia.lp` does over ℤ. A real-sorted step citing any other `RareLia`
/// entry is unsupported: `arith-geq-tighten`, `arith-int-eq-elim` and
/// `arith-leq-norm` are integer facts, and `arith-poly-norm`'s script reifies
/// over ℤ.
pub const REAL_RARE_LEMMAS: &[&str] = &[
    "arith-elim-gt",
    "arith-elim-leq",
    "arith-elim-lt",
    "arith-geq-norm1",
    "arith-geq-norm2",
    "arith-refl-geq",
    "arith-refl-gt",
    "arith-refl-leq",
    "arith-refl-lt",
];

/// [`lookup`], for a step over the given arithmetic carrier: the arithmetic
/// entries are registered over ℤ and re-routed to `alethe.rare.lra` when the
/// step is about reals.
pub fn lookup_in(name: &str, carrier: Option<Features>) -> Option<(Module, Rare)> {
    let (module, how) = lookup(name)?;
    if carrier != Some(Features::REAL) || module.feature() != Features::INT {
        return Some((module, how));
    }
    REAL_RARE_LEMMAS
        .contains(&name)
        .then_some((Module::RareLra, Rare::Lemma))
}

/// Prove a `rare_rewrite` step. `dag_terms` are the shared terms of the clause,
/// unfolded first because `rewrite` does not see through them.
pub fn translate_rare_rewrite(
    name: &str,
    how: Rare,
    step: &RareStep<'_>,
    dag_terms: HashSet<String>,
) -> Proof {
    let mut simps = dag_terms
        .into_iter()
        .map(|s| ProofStep::Simplify(vec![s]))
        .collect_vec();

    let mut rewrites = match how {
        Rare::Script(script) => script(step),
        Rare::Lemma | Rare::NatLemma => {
            let arg = |a: &Rc<AletheTerm>| match (how, a.deref()) {
                (Rare::NatLemma, AletheTerm::Const(Constant::Integer(i))) => {
                    nat(i.to_usize().expect("a width or index that fits in usize"))
                }
                _ => a.into(),
            };
            let args = step
                .args
                .iter()
                .map(arg)
                .chain(step.premises.iter().map(|(id, _)| unary_clause_to_prf(id)))
                .collect_vec();
            vec![ProofStep::Apply(
                terms![Term::from(name), ..args],
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

/// cvc5's `evaluate` folds constants; which script proves it depends on what
/// was folded and over which carrier. A comparison of two numerals is decided
/// by computation and closed with `eq_⊤_intro`/`eq_⊥_intro`; an arithmetic
/// equality is normalised by reflection over ℝ and computes over ℤ; the
/// Boolean cases are the `¬⊤`/`¬⊥` identities.
/// A comparison of two numerals, which `evaluate` decides by computation.
fn numeral_comparison(l: &AletheTerm) -> Option<(Operator, rug::Rational, rug::Rational)> {
    match l.as_op()? {
        (
            op @ (Operator::LessThan
            | Operator::LessEq
            | Operator::GreaterThan
            | Operator::GreaterEq
            | Operator::Equals),
            [a, b],
        ) => Some((op, a.as_signed_number()?, b.as_signed_number()?)),
        _ => None,
    }
}

/// Whether [`translate_evaluate`] has a script for this step. It has none for a
/// Boolean folding other than a numeral comparison, `¬⊤` and `¬⊥`, which it
/// admits; the caller proves those by `#cauto` instead when it can.
pub(crate) fn evaluate_has_script(clause: &[Rc<AletheTerm>]) -> bool {
    let Some((l, r)) = clause.first().and_then(|c| match_term!((= l r) = c)) else {
        return true;
    };
    if !(r.is_bool_true() || r.is_bool_false()) {
        return true;
    }
    numeral_comparison(l).is_some() || prop::evaluate_bool_script(l, r.is_bool_true()).is_some()
}

pub(crate) fn translate_evaluate(step: &RareStep<'_>) -> Vec<ProofStep> {
    use crate::translation::lambdapi::rules::{lia as zlia, lra};

    let cl_first = step.clause.first().expect("evaluate can not be empty");
    let Some((l, r)) = match_term!((= l r) = cl_first) else {
        panic!("not well formed evaluate, expected t1 = t2")
    };
    let real = step.carrier == Some(Features::REAL);
    if r.is_bool_true() || r.is_bool_false() {
        let truth = r.is_bool_true();
        if let Some((op, a, b)) = numeral_comparison(l) {
            return if real {
                lra::evaluate_comparison(op, &a, &b, truth)
            } else {
                zlia::evaluate_comparison(op, &a, &b, truth)
            };
        }
        // A comparison of two closed integer terms that are not numerals
        // (`(>= 3 (@bvsize x))`): decided by computation all the same.
        if !real {
            if let Some((op, [a, b])) = l.as_op() {
                if let Some(script) = zlia::evaluate_comparison_terms(op, a.into(), b.into(), truth) {
                    return script;
                }
            }
        }
        return prop::evaluate_bool_script(l, truth).unwrap_or_else(|| vec![ProofStep::Admit]);
    }
    if real {
        lra::evaluate_equality(l.into(), r.into())
    } else {
        lia::translate_evaluate_eq_arith()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::translation::lambdapi::library::declared_symbols;

    /// A `Lemma` is emitted as `apply <name>`, so the name has to be declared in
    /// the module the entry names, or the proof fails only at `lambdapi check`.
    #[test]
    fn rare_lemmas_exist_in_their_module() {
        for (name, module, how) in RARE_RULES {
            if matches!(how, Rare::Lemma | Rare::NatLemma) {
                assert!(
                    declared_symbols(*module).iter().any(|d| d == name),
                    "RARE rule `{name}` is registered as a lemma of {}, which does not declare it",
                    module.path()
                );
            }
        }
    }

    /// `arith-poly-norm` and `poly_simp` over ℤ are one `apply` of `lia.lp`'s
    /// reflection lemma, whose premise holds by conversion.
    #[test]
    fn poly_norm_applies_the_reflection_lemma() {
        assert!(declared_symbols(Module::Lia).iter().any(|d| d == "poly_norm_eq"));
        use crate::translation::lambdapi::syntax::printer::PrettyPrint;
        let script = Proof(lia::poly_norm_steps()).to_pretty();
        let script = script.split_whitespace().collect::<Vec<_>>().join(" ");
        assert_eq!(script, "apply poly_norm_eq; reflexivity;");
    }

    /// A RARE lemma missing from the registry is unreachable: a step citing it is
    /// reported as unsupported. The real lemmas are reached through `lookup_in`.
    #[test]
    fn every_rare_lemma_in_the_library_is_registered() {
        for module in [
            Module::RareProp,
            Module::RareLia,
            Module::RareLra,
            Module::RareBv,
        ] {
            for symbol in declared_symbols(module) {
                // RARE names are kebab-case; `bool-or-flatten'` and the like are helpers.
                if symbol.contains('-') && !symbol.contains('\'') {
                    let reachable = if module == Module::RareLra {
                        lookup_in(&symbol, Some(Features::REAL)).is_some_and(|(m, _)| m == module)
                    } else {
                        lookup(&symbol).is_some()
                    };
                    assert!(
                        reachable,
                        "{} declares `{symbol}`, but no rare_rewrite step can reach it",
                        module.path()
                    );
                }
            }
        }
    }

    /// Every lemma a real-sorted step is re-routed to is one `rare/lia.lp`
    /// registers and `rare/lra.lp` declares; anything else over the reals is
    /// unsupported rather than cited from the wrong module.
    #[test]
    fn real_rare_lemmas_are_re_routed() {
        let lra = declared_symbols(Module::RareLra);
        for name in REAL_RARE_LEMMAS {
            assert!(lra.iter().any(|d| d == name), "rare/lra.lp does not declare `{name}`");
            assert!(
                matches!(lookup(name), Some((Module::RareLia, Rare::Lemma))),
                "`{name}` is not registered as a lemma of rare/lia.lp"
            );
            assert_eq!(
                lookup_in(name, Some(Features::REAL)).map(|(m, _)| m),
                Some(Module::RareLra)
            );
        }
        assert!(lookup_in("arith-geq-tighten", Some(Features::REAL)).is_none());
        assert!(lookup_in("arith-poly-norm", Some(Features::REAL)).is_none());
        assert_eq!(
            lookup_in("arith-geq-tighten", Some(Features::INT)).map(|(m, _)| m),
            Some(Module::RareLia)
        );
    }

    /// A `NatLemma`'s integer arguments are the ℕ widths and indices `alethe.bv`
    /// takes, so they print as `Stdlib.Nat.n`; a term argument is unchanged.
    #[test]
    fn a_nat_lemma_prints_its_indices_as_nat() {
        use crate::parser::tests::parse_terms;
        use crate::translation::lambdapi::syntax::printer::PrettyPrint;
        let mut pool = crate::ast::pool::PrimitivePool::new();
        let [x, n, cl] = parse_terms(
            &mut pool,
            "(declare-fun x () (_ BitVec 8))",
            [
                "x",
                "63",
                "(= ((_ zero_extend 63) x) (concat (_ bv0 63) x))",
            ],
        );
        let step = RareStep {
            clause: &[cl],
            args: &[x, n],
            premises: &[],
            carrier: Some(Features::BV),
        };
        let script = translate_rare_rewrite(
            "bv-zero-extend-eliminate",
            Rare::NatLemma,
            &step,
            HashSet::new(),
        );
        let script = script
            .to_pretty()
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        assert_eq!(
            script,
            "apply ∨ᵢ₁; apply (bv-zero-extend-eliminate x Stdlib.Nat.63);"
        );
        // The same step as a plain `Lemma` would cite ℤ.
        let script = translate_rare_rewrite(
            "bv-zero-extend-eliminate",
            Rare::Lemma,
            &step,
            HashSet::new(),
        );
        assert!(script.to_pretty().contains("Stdlib.Z.63"));
    }

    #[test]
    fn a_rule_is_registered_once() {
        for (i, (name, ..)) in RARE_RULES.iter().enumerate() {
            assert!(
                !RARE_RULES[i + 1..].iter().any(|(n, ..)| n == name),
                "`{name}` is registered twice"
            );
        }
    }
}
