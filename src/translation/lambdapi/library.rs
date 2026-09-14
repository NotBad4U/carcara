//! The modules of the `alethe` Lambdapi package in `alethe-lp/`.
//!
//! The cvc5 RARE rewrites over a theory live in a companion module under
//! `alethe-lp/rare/`, apart from the Alethe rules of that theory. A
//! `rare_rewrite` step cites them by the RARE rule's name.

use super::logic::Features;

/// A module of the `alethe` package that a generated proof can `require open`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Module {
    Core,
    Prop,
    Quant,
    Lia,
    Lra,
    RareProp,
    RareLia,
    RareLra,
}

impl Module {
    /// Every module, in the order a header opens them: each `rare/` module right
    /// after the theory module it extends, and the arithmetic carrier last, since
    /// the last module opened decides what a bare numeral means.
    pub const ALL: [Self; 8] = [
        Self::Core,
        Self::Prop,
        Self::RareProp,
        Self::Quant,
        Self::Lia,
        Self::RareLia,
        Self::Lra,
        Self::RareLra,
    ];

    /// The path a generated proof requires.
    #[must_use]
    pub const fn path(self) -> &'static str {
        match self {
            Self::Core => "alethe.core",
            Self::Prop => "alethe.prop",
            Self::Quant => "alethe.quant",
            Self::Lia => "alethe.lia",
            Self::Lra => "alethe.lra",
            Self::RareProp => "alethe.rare.prop",
            Self::RareLia => "alethe.rare.lia",
            Self::RareLra => "alethe.rare.lra",
        }
    }

    /// The theory feature that opens this module. A `rare/` module shares its
    /// theory module's feature, so the two are always opened together.
    #[must_use]
    pub const fn feature(self) -> Features {
        match self {
            Self::Core | Self::Prop | Self::RareProp => Features::EMPTY,
            Self::Quant => Features::QUANT,
            Self::Lia | Self::RareLia => Features::INT,
            Self::Lra | Self::RareLra => Features::REAL,
        }
    }
}

/// The symbols a module's source file declares, for the tests that check every
/// name the translator emits for a rule against the library.
#[cfg(test)]
pub(crate) fn declared_symbols(module: Module) -> Vec<String> {
    let file = format!(
        "alethe-lp/{}.lp",
        module.path().trim_start_matches("alethe.").replace('.', "/")
    );
    std::fs::read_to_string(&file)
        .unwrap_or_else(|e| panic!("cannot read {file}: {e}"))
        .lines()
        .filter_map(|l| l.split_once("symbol "))
        .map(|(_, rest)| rest.split([' ', ':', '[', '(']).next().unwrap_or("").to_owned())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_module_has_a_source_file() {
        for m in Module::ALL {
            declared_symbols(m);
        }
    }

    #[test]
    fn a_rare_module_comes_right_after_its_theory_module() {
        for (theory, rare) in [
            (Module::Prop, Module::RareProp),
            (Module::Lia, Module::RareLia),
            (Module::Lra, Module::RareLra),
        ] {
            let at = |m| Module::ALL.iter().position(|x| *x == m).unwrap();
            assert_eq!(at(rare), at(theory) + 1, "{rare:?}");
            assert!(theory.feature() == rare.feature(), "{rare:?}");
        }
    }
}
