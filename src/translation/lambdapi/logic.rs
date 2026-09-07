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

    pub const ALL: Self = Self(0xff);

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

/// How a logic name was resolved.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LogicKind {
    /// One of the 25 names in the standard.
    Standard,
    /// `ALL`, a missing `(set-logic …)`, or a name solvers accept but the
    /// standard does not list (`UFLIA`, `HORN`, …). Every feature is assumed.
    Unrecognised,
}

/// Features declared by `(set-logic …)`. A missing or unrecognised logic
/// yields every feature, so nothing is silently left out of the header.
#[must_use]
pub fn features_of_logic(logic: Option<&str>) -> (Features, LogicKind) {
    match logic {
        Some(name) => match STANDARD_LOGICS.iter().find(|(n, _)| *n == name) {
            Some((_, f)) => (*f, LogicKind::Standard),
            None => (Features::ALL, LogicKind::Unrecognised),
        },
        None => (Features::ALL, LogicKind::Unrecognised),
    }
}

/// The Lambdapi modules a proof with these features must `require open`, in
/// the order they have to be opened.
///
/// The order is load-bearing: decimal notation can only be bound to one type at
/// a time, so the last arithmetic module opened decides what a numeral means
/// (see <https://github.com/Deducteam/lambdapi/issues/1268>).
#[must_use]
pub fn modules(used: Features) -> Vec<&'static str> {
    let mut m = vec!["alethe.core", "alethe.prop"];

    // Gated on what the proof used, not on what the logic declared: an
    // unrecognised logic declares everything, and `quant.lp` carries the Hilbert
    // choice axioms, which have no business in a quantifier-free proof.
    if used.contains(Features::QUANT) {
        m.push("alethe.quant");
    }

    // Gated on the feature now that clause indices are rendered as qualified
    // `Stdlib.Nat` constants. They used to go through `int2nat`, which lives here
    // and exists only to undo this module's own re-pinning of the decimal
    // notation to ℤ -- so the header had to open it unconditionally, and every
    // proof inherited the integer layer's admits. See REFACTORING.md, friction 3.
    if used.contains(Features::INT) {
        m.push("alethe.lia");
    }

    // Likewise gated on use, never on declaration. `lia` and `lra` must not both
    // be opened: they declare the same reification machinery (`G`, `Cst`, `Var`,
    // `rec_G`, `reify`, ...), and `lia` re-pins the decimal notation to ℤ.
    if used.contains(Features::REAL) {
        m.push("alethe.lra");
    }
    m
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_standard_logic_maps_to_existing_modules() {
        let available = [
            "alethe.core",
            "alethe.prop",
            "alethe.quant",
            "alethe.lia",
            "alethe.lra",
        ];
        assert_eq!(STANDARD_LOGICS.len(), 25, "the standard defines 25 logics");
        for (name, _) in STANDARD_LOGICS {
            let (f, kind) = features_of_logic(Some(name));
            assert_eq!(kind, LogicKind::Standard, "{name}");
            // Worst case: a proof that used everything the logic declares.
            for m in modules(f) {
                assert!(available.contains(&m), "{name} wants a missing module {m}");
            }
        }
    }

    #[test]
    fn quantifier_free_logics_do_not_pull_the_quantifier_module() {
        for (name, _) in STANDARD_LOGICS.iter().filter(|(n, _)| n.starts_with("QF_")) {
            let (f, _) = features_of_logic(Some(name));
            assert!(!f.contains(Features::QUANT), "{name}");
            // ... so not even a proof using every declared feature opens it.
            assert!(!modules(f).contains(&"alethe.quant"), "{name}");
        }
    }

    #[test]
    fn unknown_and_missing_logics_assume_everything() {
        for l in [None, Some("ALL"), Some("UFLIA"), Some("HORN"), Some("QF_LIRA")] {
            let (f, kind) = features_of_logic(l);
            assert_eq!(kind, LogicKind::Unrecognised, "{l:?}");
            assert!(f.contains(Features::QUANT) && f.contains(Features::INT), "{l:?}");
        }
    }

    #[test]
    fn arithmetic_logics_select_their_carrier() {
        let int = |n| features_of_logic(Some(n)).0;
        assert!(int("QF_LIA").contains(Features::INT));
        assert!(!int("QF_LIA").contains(Features::REAL));
        assert!(int("QF_LRA").contains(Features::REAL));
        assert!(!int("QF_LRA").contains(Features::INT));
        // The only standard logics with both carriers also need arrays.
        for n in ["AUFLIRA", "AUFNIRA"] {
            let f = int(n);
            assert!(f.contains(Features::INT) && f.contains(Features::REAL), "{n}");
            assert!(f.contains(Features::ARRAY), "{n}");
        }
    }

    #[test]
    fn an_unrecognised_logic_drags_in_no_arithmetic_at_all() {
        // An unrecognised logic declares every feature, and none of that may reach
        // the header: `lia` and `lra` are mutually exclusive, and both carry admits
        // a propositional proof has no reason to inherit. `modules` now takes only
        // what was used, so declaration cannot leak in by construction.
        assert_eq!(features_of_logic(None).0, Features::ALL);
        let m = modules(Features::EMPTY);
        assert_eq!(m, vec!["alethe.core", "alethe.prop"], "{m:?}");

        // ... but a proof that really used a carrier still gets it, and only it.
        let int = modules(Features::INT);
        assert!(int.contains(&"alethe.lia") && !int.contains(&"alethe.lra"), "{int:?}");
        let real = modules(Features::REAL);
        assert!(real.contains(&"alethe.lra") && !real.contains(&"alethe.lia"), "{real:?}");
    }

    #[test]
    fn the_quantifier_layer_follows_use_not_declaration() {
        // `quant.lp` carries the Hilbert choice axioms. An unrecognised logic
        // declares QUANT, but that must not by itself open the module.
        let (declared, _) = features_of_logic(Some("UF"));
        assert!(declared.contains(Features::QUANT), "UF is unrecognised, so declares all");
        assert!(!modules(Features::EMPTY).contains(&"alethe.quant"));
        assert!(modules(Features::QUANT).contains(&"alethe.quant"));
    }

    #[test]
    fn unsupported_features_are_reported() {
        assert!(!features_of_logic(Some("QF_BV")).0.unsupported().is_empty());
        assert!(!features_of_logic(Some("AUFLIA")).0.unsupported().is_empty());
        assert!(features_of_logic(Some("QF_UF")).0.unsupported().is_empty());
        assert!(features_of_logic(Some("QF_LIA")).0.unsupported().is_empty());
        assert!(features_of_logic(Some("UFNIA")).0.unsupported().is_empty());
    }
}
