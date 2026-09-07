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
