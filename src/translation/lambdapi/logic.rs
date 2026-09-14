//! SMT-LIB logic names, the theory features they imply, and the Lambdapi
//! library modules those features need.
//!
//! The standard defines exactly 25 logics (<https://smt-lib.org/logics.shtml>)
//! and that set is *not* closed under the feature combinations that occur:
//! there is no `UF`, no `UFLIA`, no `AUFLRA` and no `LIRA`. A declared logic is
//! therefore always an over-approximation of what a proof actually uses, which
//! is why [`Features`] is also accumulated from the rules as they are
//! translated and compared against the declaration.

use std::fmt;

use super::library::Module;

/// A set of theory features. Built from `(set-logic …)` and widened by the
/// rules a proof actually uses.
#[derive(Clone, Copy, PartialEq, Eq, Default)]
pub struct Features(u16);

impl Features {
    pub const EMPTY: Self = Self(0);
    /// The logic is not quantifier-free.
    pub const QUANT: Self = Self(1 << 0);
    pub const INT: Self = Self(1 << 1);
    pub const REAL: Self = Self(1 << 2);
    pub const ARRAY: Self = Self(1 << 3);
    pub const BV: Self = Self(1 << 4);
    /// Non-linear arithmetic. Adds no module: the linear layer covers whatever
    /// stays linear, and genuinely non-linear steps are unsupported.
    pub const NONLINEAR: Self = Self(1 << 5);
    /// Integer exponentiation (`QF_EIA`).
    pub const EXP: Self = Self(1 << 6);

    /// Uninterpreted functions need no module of their own: they are served by
    /// the congruence rules in `core` and by the `declare-fun` emission in the
    /// generated proof's preamble. Tracked only so diagnostics can name it.
    pub const UF: Self = Self(1 << 7);

    #[must_use]
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// The features in `self` that are not in `other`.
    #[must_use]
    pub const fn difference(self, other: Self) -> Self {
        Self(self.0 & !other.0)
    }

    /// The features this backend has no rules for at all.
    #[must_use]
    pub const fn unsupported(self) -> Self {
        Self(self.0 & Self::ARRAY.union(Self::BV).union(Self::EXP).0)
    }

    fn names(self) -> Vec<&'static str> {
        [
            (Self::QUANT, "quantifiers"),
            (Self::UF, "uninterpreted functions"),
            (Self::INT, "integer arithmetic"),
            (Self::REAL, "real arithmetic"),
            (Self::NONLINEAR, "non-linear arithmetic"),
            (Self::ARRAY, "arrays"),
            (Self::BV, "bit-vectors"),
            (Self::EXP, "exponentiation"),
        ]
        .into_iter()
        .filter(|(f, _)| self.contains(*f))
        .map(|(_, n)| n)
        .collect()
    }
}

impl std::ops::BitOr for Features {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        self.union(rhs)
    }
}

impl std::ops::BitOrAssign for Features {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl fmt::Debug for Features {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let n = self.names();
        if n.is_empty() {
            write!(f, "(none)")
        } else {
            write!(f, "{}", n.join(", "))
        }
    }
}

/// The 25 logics of the SMT-LIB standard, and the features each implies.
/// `QF_` is not stripped and re-parsed: the names are irregular enough
/// (`QF_AX`, `QF_EIA`, `QF_UFIDL`, `AUFNIRA`) that a table is both simpler and
/// directly testable.
const STANDARD_LOGICS: &[(&str, Features)] = &{
    use Features as F;
    [
        ("AUFLIA", F::QUANT.union(F::ARRAY).union(F::UF).union(F::INT)),
        ("AUFLIRA", F::QUANT.union(F::ARRAY).union(F::UF).union(F::INT).union(F::REAL)),
        ("AUFNIRA", F::QUANT.union(F::ARRAY).union(F::UF).union(F::INT).union(F::REAL).union(F::NONLINEAR)),
        ("LIA", F::QUANT.union(F::INT)),
        ("LRA", F::QUANT.union(F::REAL)),
        ("QF_ABV", F::ARRAY.union(F::BV)),
        ("QF_AUFBV", F::ARRAY.union(F::UF).union(F::BV)),
        ("QF_AUFLIA", F::ARRAY.union(F::UF).union(F::INT)),
        ("QF_AX", F::ARRAY),
        ("QF_BV", F::BV),
        ("QF_EIA", F::INT.union(F::EXP)),
        ("QF_IDL", F::INT),
        ("QF_LIA", F::INT),
        ("QF_LRA", F::REAL),
        ("QF_NIA", F::INT.union(F::NONLINEAR)),
        ("QF_NRA", F::REAL.union(F::NONLINEAR)),
        ("QF_RDL", F::REAL),
        ("QF_UF", F::UF),
        ("QF_UFBV", F::UF.union(F::BV)),
        ("QF_UFIDL", F::UF.union(F::INT)),
        ("QF_UFLIA", F::UF.union(F::INT)),
        ("QF_UFLRA", F::UF.union(F::REAL)),
        ("QF_UFNRA", F::UF.union(F::REAL).union(F::NONLINEAR)),
        ("UFLRA", F::QUANT.union(F::UF).union(F::REAL)),
        ("UFNIA", F::QUANT.union(F::UF).union(F::INT).union(F::NONLINEAR)),
    ]
};

/// Features declared by `(set-logic …)`, or `None` when the declaration is not
/// one of the 25 standard names: `ALL`, a missing `(set-logic …)`, or a name
/// solvers accept but the standard does not list (`UF`, `UFLIA`, `HORN`, …).
///
/// `None` rather than every feature, because the header opens what a logic
/// declares: an unrecognised logic declaring everything would open `lia` and
/// `lra` together, and put the Hilbert choice axioms and the ℤ layer's admits
/// into proofs that use neither.
#[must_use]
pub fn features_of_logic(logic: Option<&str>) -> Option<Features> {
    let name = logic?;
    STANDARD_LOGICS
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, f)| *f)
}

/// The Lambdapi modules a proof must `require open`, in the order they have to
/// be opened.
///
/// A standard logic opens the theory modules its features need, whether or not
/// the proof's steps use them, and what the steps use widens that. An
/// unrecognised logic (`declared` is `None`) opens nothing by itself, so its
/// header is exactly what the steps use. `INT` also answers for `Stdlib.Z`,
/// where the `Stdlib.Z.n` numerals and the `int` sort name come from, which is
/// why integer literals and Int sorts set it in `mod.rs`.
///
/// Every `rare/` module is opened with its theory module, whether or not a step
/// cites one of its lemmas. Gating them on the `rare_rewrite` steps is a later
/// refinement.
///
/// The order is load-bearing: decimal notation can only be bound to one type at
/// a time, so the last arithmetic module opened decides what a numeral means
/// (see <https://github.com/Deducteam/lambdapi/issues/1268>).
#[must_use]
pub fn modules(declared: Option<Features>, used: Features) -> Vec<Module> {
    let carriers = Features::INT.union(Features::REAL);
    let floor = match declared {
        // `lia` and `lra` must not both be opened: they declare the same
        // reification machinery (`G`, `Cst`, `Var`, `rec_G`, `reify`, ...). A
        // logic declaring both carriers (`AUFLIRA`, `AUFNIRA`) therefore opens
        // neither by itself, and arithmetic follows what the proof uses.
        Some(f) if f.contains(carriers) => f.difference(carriers),
        Some(f) => f,
        None => Features::EMPTY,
    };
    let needed = floor.union(used);
    Module::ALL
        .into_iter()
        .filter(|m| needed.contains(m.feature()))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use Module as M;

    fn header(logic: &str, used: Features) -> Vec<Module> {
        modules(features_of_logic(Some(logic)), used)
    }

    #[test]
    fn the_standard_defines_25_logics() {
        assert_eq!(STANDARD_LOGICS.len(), 25, "the standard defines 25 logics");
        for (name, _) in STANDARD_LOGICS {
            assert!(features_of_logic(Some(name)).is_some(), "{name}");
        }
    }

    #[test]
    fn a_standard_logic_opens_its_theory_modules_without_use() {
        assert_eq!(header("QF_UF", Features::EMPTY), [M::Core, M::Prop, M::RareProp]);
        assert_eq!(
            header("QF_LIA", Features::EMPTY),
            [M::Core, M::Prop, M::RareProp, M::Lia, M::RareLia]
        );
        assert_eq!(
            header("LRA", Features::EMPTY),
            [M::Core, M::Prop, M::RareProp, M::Quant, M::Lra, M::RareLra]
        );
    }

    #[test]
    fn use_widens_a_standard_logic() {
        // An integer literal in a QF_UF proof needs `Stdlib.Z`, reached through `lia`.
        assert!(header("QF_UF", Features::INT).contains(&M::Lia));
    }

    #[test]
    fn quantifier_free_logics_do_not_pull_the_quantifier_module() {
        for (name, f) in STANDARD_LOGICS.iter().filter(|(n, _)| n.starts_with("QF_")) {
            assert!(!f.contains(Features::QUANT), "{name}");
            // ... so not even a proof using every declared feature opens it.
            assert!(!header(name, *f).contains(&M::Quant), "{name}");
        }
    }

    #[test]
    fn a_rare_module_is_opened_with_its_theory_module() {
        for (name, f) in STANDARD_LOGICS {
            for h in [header(name, Features::EMPTY), header(name, *f)] {
                for (theory, rare) in [(M::Prop, M::RareProp), (M::Lia, M::RareLia), (M::Lra, M::RareLra)] {
                    assert_eq!(h.contains(&theory), h.contains(&rare), "{name}: {h:?}");
                }
            }
        }
    }

    #[test]
    fn no_declaration_opens_both_carriers() {
        for (name, _) in STANDARD_LOGICS {
            let h = header(name, Features::EMPTY);
            assert!(!(h.contains(&M::Lia) && h.contains(&M::Lra)), "{name}: {h:?}");
        }
        // The only standard logics with both carriers also need arrays.
        for n in ["AUFLIRA", "AUFNIRA"] {
            let f = features_of_logic(Some(n)).unwrap();
            assert!(f.contains(Features::INT) && f.contains(Features::REAL), "{n}");
            assert!(f.contains(Features::ARRAY), "{n}");
        }
    }

    #[test]
    fn unknown_and_missing_logics_declare_nothing() {
        for l in [None, Some("ALL"), Some("UF"), Some("UFLIA"), Some("HORN"), Some("QF_LIRA")] {
            assert_eq!(features_of_logic(l), None, "{l:?}");
        }
    }

    #[test]
    fn an_unrecognised_logic_opens_only_what_the_proof_uses() {
        // Neither the ℤ layer's admits nor the Hilbert choice axioms in `quant.lp`
        // reach a proof whose logic says nothing reliable and whose steps use
        // neither.
        assert_eq!(modules(None, Features::EMPTY), [M::Core, M::Prop, M::RareProp]);

        // ... but a proof that really used a carrier or a quantifier still gets
        // it, and only it.
        let int = modules(None, Features::INT);
        assert!(int.contains(&M::Lia) && !int.contains(&M::Lra), "{int:?}");
        let real = modules(None, Features::REAL);
        assert!(real.contains(&M::Lra) && !real.contains(&M::Lia), "{real:?}");
        assert!(modules(None, Features::QUANT).contains(&M::Quant));
    }

    #[test]
    fn arithmetic_logics_select_their_carrier() {
        let f = |n| features_of_logic(Some(n)).unwrap();
        assert!(f("QF_LIA").contains(Features::INT));
        assert!(!f("QF_LIA").contains(Features::REAL));
        assert!(f("QF_LRA").contains(Features::REAL));
        assert!(!f("QF_LRA").contains(Features::INT));
    }

    #[test]
    fn unsupported_features_are_reported() {
        let f = |n| features_of_logic(Some(n)).unwrap();
        assert!(!f("QF_BV").unsupported().is_empty());
        assert!(!f("AUFLIA").unsupported().is_empty());
        assert!(f("QF_UF").unsupported().is_empty());
        assert!(f("QF_LIA").unsupported().is_empty());
        assert!(f("UFNIA").unsupported().is_empty());
    }
}
