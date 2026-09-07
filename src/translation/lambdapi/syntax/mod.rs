//! The Lambdapi syntax tree and its rendering: terms, proof scripts, the
//! `lambdapi!` DSL, the pretty printer and the file containers. Nothing here
//! knows about Alethe rules.

#[macro_use]
pub mod term;

mod dsl;
pub mod output;
pub mod printer;
pub mod proof;

pub(crate) use dsl::*;
pub use output::*;
pub use proof::*;
pub use term::*;
