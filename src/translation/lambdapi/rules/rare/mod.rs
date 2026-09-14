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
use crate::translation::lambdapi::*;
use std::ops::Deref;

/// What a script for a RARE rule gets to see of its step.
pub struct RareStep<'a> {
    pub clause: &'a [Rc<AletheTerm>],
    /// The rule's arguments, without the rule name.
    pub args: &'a [Rc<AletheTerm>],
    /// The step's premises: the conditions of a `define-cond-rule`, in order.
    pub premises: &'a [(String, &'a [Rc<AletheTerm>])],
}

/// How the backend proves a RARE rule.
#[derive(Clone, Copy)]
pub enum Rare {
    /// `apply` the library lemma named after the rule to the step's arguments,
    /// then to its premises. A `define-cond-rule` lemma takes its conditions as
    /// hypotheses after its variables.
    Lemma,
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
    use Module::{Core, Lia, RareLia, RareProp};
    use Rare::{Lemma, Script};
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
        Rare::Lemma => {
            let args = step
                .args
                .iter()
                .map(std::convert::Into::into)
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
/// was folded.
fn translate_evaluate(step: &RareStep<'_>) -> Vec<ProofStep> {
    let cl_first = step.clause.first().expect("evaluate can not be empty");
    match match_term!((= l r) = cl_first) {
        Some((l, r))
            if (r.is_bool_false() || r.is_bool_true())
                && (matches!(l.deref(), AletheTerm::Op(Operator::GreaterEq, _))
                    || matches!(l.deref(), AletheTerm::Op(Operator::LessEq, _))
                    || matches!(l.deref(), AletheTerm::Op(Operator::GreaterThan, _))
                    || matches!(l.deref(), AletheTerm::Op(Operator::LessThan, _))) =>
        {
            lia::translate_evaluate_linear_arith()
        }
        Some((_l, r)) if (r.is_bool_false() || r.is_bool_true()) => {
            prop::translate_evaluate_bool()
        }
        Some(_) => lia::translate_evaluate_eq_arith(),
        None => panic!("not well formed evaluate, expected t1 = t2"),
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
            if matches!(how, Rare::Lemma) {
                assert!(
                    declared_symbols(*module).iter().any(|d| d == name),
                    "RARE rule `{name}` is registered as a lemma of {}, which does not declare it",
                    module.path()
                );
            }
        }
    }

    /// A RARE lemma missing from the registry is unreachable: a step citing it is
    /// reported as unsupported.
    #[test]
    fn every_rare_lemma_in_the_library_is_registered() {
        for module in [Module::RareProp, Module::RareLia, Module::RareLra] {
            for symbol in declared_symbols(module) {
                // RARE names are kebab-case; `bool-or-flatten'` and the like are helpers.
                if symbol.contains('-') && !symbol.contains('\'') {
                    assert!(
                        lookup(&symbol).is_some(),
                        "{} declares `{symbol}`, but no rare_rewrite step can reach it",
                        module.path()
                    );
                }
            }
        }
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
