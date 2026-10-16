//! The BNF grammar of Lambdapi is in [lambdapi.bnf](https://raw.githubusercontent.com/Deducteam/lambdapi/master/doc/lambdapi.bnf).
//! Data structure of this file try to represent this grammar.
//!
use crate::ast::{
    Binder as AletheBinder, BindingList, Constant, Operator, ParamOperator, Rc, Sort, SortedVar,
    Term as AletheTerm,
    pool::{PrimitivePool, TermPool},
};
use itertools::Itertools;
use rug::{Integer, Rational};
use std::borrow::Borrow;
use std::collections::{HashSet, VecDeque};
use std::ops::Deref;
use std::{fmt, vec};

const WHITE_SPACE: &str = " ";

use super::super::Context;
use super::proof::Proof;

#[inline]
pub fn set() -> Term {
    Term::TermId("Set".into())
}

#[inline]
pub fn omicron() -> Term {
    Term::TermId("o".into())
}

/// `τ t`, the interpretation of a sort code as a type.
///
/// An application rather than the pre-rendered string `"τ (…)"`, so that
/// `Term::TermId` keeps holding a bare identifier -- see `operator_section`. Rendered
/// through `Display` it used to smuggle a whole type expression into a name, which
/// the printer then escaped wholesale as `{|τ (A_literal_multiset$)|}`.
#[inline]
pub fn tau(term: Term) -> Term {
    // The argument is wrapped so that it keeps its parentheses: `τ` binds tighter
    // than `⤳`, so a sort like `A ⤳ B` has to stay grouped.
    Term::Terms(vec![Term::TermId("τ".into()), Term::Terms(vec![term])])
}

#[inline]
pub fn proof(term: Term) -> Term {
    Term::Alethe(LTerm::Proof(Box::new(term)))
}

/// A ℕ literal, `Stdlib.Nat.n`: a bit-vector width, the index of an indexed
/// operator, the arity of a `bbterm`.
#[inline]
pub fn nat(n: usize) -> Term {
    Term::Nat(u32::try_from(n).expect("a ℕ literal that fits in 32 bits"))
}

/// The sort `(_ BitVec n)`: `bitvec Stdlib.Nat.n`, the quotient `ℕ ⫽ (≈ n)` of
/// `alethe.bv`. An application, like `tau`, so that the width stays a separate
/// token the printer scopes against `Stdlib.Nat`.
#[inline]
pub fn bitvec_sort(n: usize) -> Term {
    Term::Terms(vec![Term::TermId("bitvec".into()), nat(n)])
}

/// A `Stdlib.List` literal, `(t₁ ⸬ … ⸬ tₙ ⸬ □)`, in the order given.
#[inline]
pub fn lp_list(terms: Vec<Term>) -> Term {
    Term::Alethe(LTerm::List(List(terms)))
}

/// A bit-vector literal -- `#b0110` and `(_ bv6 4)` both arrive as
/// `Constant::BitVec` -- as `alethe.bv` spells it: `bvlit Stdlib.Nat.w (d₀ ⸬ … ⸬
/// d_{w-1} ⸬ □)`, the digits least significant first, each the `Stdlib.Bool`
/// constructor `true` or `false` (`alethe.core` opens `Stdlib.Bool`, so they
/// resolve unqualified). A digit list rather than a numeral because `Stdlib.Nat`
/// is unary: `class (≈ 32) 2147483648` would hang the first conversion check,
/// while comparing two 32-bit literals is 32 cell comparisons.
pub fn bv_literal(value: &Integer, width: usize) -> Term {
    let digits = (0..width)
        .map(|i| {
            let i = u32::try_from(i).expect("a bit-vector width that fits in 32 bits");
            Term::from(if value.get_bit(i) { "true" } else { "false" })
        })
        .collect_vec();
    Term::Terms(vec![
        Term::TermId("bvlit".into()),
        nat(width),
        lp_list(digits),
    ])
}

/// The `alethe.bv` symbol of a bit-vector operator: its SMT-LIB name, cvc5's
/// internal `@`-prefixed ones without the `@`. `None` if `op` is not a
/// bit-vector operator.
pub(crate) fn bv_op_name(op: Operator) -> Option<&'static str> {
    use Operator as O;
    Some(match op {
        O::BvNot => "bvnot",
        O::BvNeg => "bvneg",
        O::BvAnd => "bvand",
        O::BvOr => "bvor",
        O::BvAdd => "bvadd",
        O::BvMul => "bvmul",
        O::BvUDiv => "bvudiv",
        O::BvURem => "bvurem",
        O::BvShl => "bvshl",
        O::BvLShr => "bvlshr",
        O::BvULt => "bvult",
        O::BvConcat => "concat",
        O::BvNAnd => "bvnand",
        O::BvNOr => "bvnor",
        O::BvXor => "bvxor",
        O::BvXNor => "bvxnor",
        O::BvComp => "bvcomp",
        O::BvSub => "bvsub",
        O::BvSDiv => "bvsdiv",
        O::BvSRem => "bvsrem",
        O::BvSMod => "bvsmod",
        O::BvAShr => "bvashr",
        O::BvULe => "bvule",
        O::BvUGt => "bvugt",
        O::BvUGe => "bvuge",
        O::BvSLt => "bvslt",
        O::BvSLe => "bvsle",
        O::BvSGt => "bvsgt",
        O::BvSGe => "bvsge",
        O::UBvToInt => "ubv_to_int",
        O::SBvToInt => "sbv_to_int",
        O::BvPBbTerm => "pbbterm",
        O::BvBbTerm => "bbterm",
        // `@bv v w` with numeral arguments is printed as the literal it denotes
        // (see `bv_op`); this name is for the symbolic case, `alethe.bvint`'s.
        O::BvConst => "bv_of_int",
        O::BvSize => "bvsize",
        O::BvIte => "bvite",
        _ => return None,
    })
}

/// The bit-vector operators SMT-LIB declares `:left-assoc` (and `concat`, which
/// cvc5 also writes n-ary): `(bvadd a b c)` is `bvadd (bvadd a b) c`, and
/// `(concat a b c)`'s last argument is the low part.
const LEFT_FOLDED_BV_OPS: [Operator; 6] = [
    Operator::BvAdd,
    Operator::BvMul,
    Operator::BvAnd,
    Operator::BvOr,
    Operator::BvXor,
    Operator::BvConcat,
];

/// Is this operator folded to the left when it has more than two arguments?
/// `cong` nests its `feq2` chain the same way (see `rules::core::feq2_chain`).
pub(crate) fn is_left_folded(op: Operator) -> bool {
    LEFT_FOLDED_BV_OPS.contains(&op) || op == Operator::Xor
}

/// A bit-vector operation as `alethe.bv` writes it: a prefix application of
/// the operator's name, the n-ary ones folded to the left (`LEFT_FOLDED_BV_OPS`).
/// cvc5's `@bbterm b₀ … bₙ₋₁` is `bbterm Stdlib.Nat.n (b₀ ⸬ … ⸬ bₙ₋₁ ⸬ □)` --
/// the bits least significant first, as cvc5 lists them -- and `@bv v w` with
/// numeral arguments is the literal `bv_literal` prints for `(_ bvv w)`.
/// `None` if `op` is not a bit-vector operator.
pub(crate) fn bv_op(op: Operator, alethe_args: &[Rc<AletheTerm>], args: Vec<Term>) -> Option<Term> {
    let name = bv_op_name(op)?;
    let numeral = |k: usize| alethe_args.get(k).and_then(|a| a.as_integer());
    Some(match op {
        Operator::BvBbTerm => Term::Terms(vec![Term::from(name), nat(args.len()), lp_list(args)]),
        Operator::BvConst => match (numeral(0), numeral(1).and_then(|w| w.to_usize())) {
            (Some(v), Some(w)) => bv_literal(&v, w),
            // A symbolic value: `alethe.bvint`'s `bv_of_int w z`, the width first
            // and as a ℕ numeral, as the library declares it.
            (None, Some(w)) => Term::Terms(vec![
                Term::from(name),
                nat(w),
                args.into_iter().next().expect("@bv has a value"),
            ]),
            _ => Term::Terms(std::iter::once(Term::from(name)).chain(args).collect()),
        },
        o if LEFT_FOLDED_BV_OPS.contains(&o) => args
            .into_iter()
            .reduce(|acc, arg| Term::Terms(vec![Term::from(name), acc, arg]))
            .expect("a bit-vector operation has at least one argument"),
        _ => Term::Terms(std::iter::once(Term::from(name)).chain(args).collect()),
    })
}

/// The `alethe.bv` symbol of an indexed bit-vector operator, or `None` for one
/// the library has no symbol for.
pub(crate) fn param_op_name(op: ParamOperator) -> Option<&'static str> {
    Some(match op {
        ParamOperator::BvExtract => "extract",
        ParamOperator::BvBitOf => "bit_of",
        ParamOperator::ZeroExtend => "zero_extend",
        ParamOperator::SignExtend => "sign_extend",
        ParamOperator::RotateLeft => "rotate_left",
        ParamOperator::RotateRight => "rotate_right",
        ParamOperator::Repeat => "repeat",
        _ => return None,
    })
}

/// The indices of an indexed operator as ℕ literals, `None` if one is not a
/// numeral.
pub(crate) fn param_op_indices(op_args: &[Rc<AletheTerm>]) -> Option<Vec<Term>> {
    op_args
        .iter()
        .map(|i| i.as_integer()?.to_usize().map(nat))
        .collect()
}

/// An indexed bit-vector operation, `((_ extract i j) x)`: `extract Stdlib.Nat.i
/// Stdlib.Nat.j x`, the indices first, as `alethe.bv` declares its symbols
/// (`extract [n] (i j : ℕ) : τ (bitvec n) → …`; the width stays implicit and is
/// inferred from `x`). `None` for an operator the library has no symbol for, or
/// whose indices are not numerals.
pub(crate) fn param_op(
    op: ParamOperator,
    op_args: &[Rc<AletheTerm>],
    args: Vec<Term>,
) -> Option<Term> {
    let name = param_op_name(op)?;
    let indices = param_op_indices(op_args)?;
    Some(Term::Terms(
        std::iter::once(Term::from(name))
            .chain(indices)
            .chain(args)
            .collect(),
    ))
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum BuiltinSort {
    /// a non-dependent function A ⤳ T where A and T are Set
    Arrow(Box<Term>, Box<Term>),
    Bool,
    Int, //FIXME: We use ℤ because some feature in ℤ encoding are missing in Stdlib.Z
    /// `alethe.real`'s carrier, reached through `alethe.lra`.
    Real,
}

impl fmt::Display for BuiltinSort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BuiltinSort::Arrow(a, b) => write!(f, "{} ⤳ {}", a, b),
            BuiltinSort::Bool => write!(f, "o"),
            BuiltinSort::Int => write!(f, "int"),
            BuiltinSort::Real => write!(f, "real"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Modifier {
    Constant,
    Opaque,
}

impl fmt::Display for Modifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Modifier::Constant => write!(f, "constant"),
            Modifier::Opaque => write!(f, "opaque"),
        }
    }
}

/// The Grammar <command> token
#[derive(Debug, Clone, PartialEq)]
pub enum Command {
    RequireOpen(String),
    /// Symbol declaration with a proof script (theorem or interactive definition)
    Symbol(Option<Modifier>, String, Vec<Param>, Term, Option<Proof>),
    /// Symbol declaration with an optional definition
    Definition(String, Vec<Param>, Option<Term>, Option<Term>),
    Rule(Term, Term),
}

impl Command {
    pub fn id(&self) -> Option<String> {
        match self {
            Command::Symbol(_, id, ..) => Some(id.clone()),
            Command::Definition(id, ..) => Some(id.clone()),
            _ => None,
        }
    }
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Command::RequireOpen(path) => write!(f, "open require {};", path),
            Command::Symbol(modifier, name, params, term, proof) => {
                let params = params
                    .iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<_>>()
                    .join(WHITE_SPACE);
                write!(
                    f,
                    "{}symbol {} {}: {}",
                    modifier
                        .as_ref()
                        .map_or(String::new(), |m| format!("{} ", m)),
                    name,
                    params,
                    term
                )?;

                if let Some(proof) = proof {
                    writeln!(f, " ≔")?;
                    writeln!(f, "begin")?;
                    write!(f, "{}", proof)?;
                    write!(f, "\nend")?;
                }
                writeln!(f, ";")
            }
            Command::Definition(name, params, r#type, definition) => {
                let params = params
                    .iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<_>>()
                    .join(WHITE_SPACE);
                write!(f, "symbol {} {}", name, params)?;
                if let Some(r#ty) = r#type {
                    write!(f, " : {}", r#ty)?;
                }
                if let Some(def) = definition {
                    write!(f, " ≔ {}", def)?;
                }
                //write!(f, "symbol {} {} : {} ≔ {};", name, params, r#type, definition)
                writeln!(f, ";")
            }
            Command::Rule(l, r) => writeln!(f, "rule {} ↪ {};", l, r),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Term {
    Alethe(LTerm),
    Sort(BuiltinSort),
    TermId(String),
    Terms(Vec<Term>),
    Function(Vec<Term>),
    Nat(u32),
    Int(Integer),
    /// A real literal, `lit (n / d)`.
    Real(Rational),
    /// A positive numeral, ℙ: the denominator of a real literal.
    Pos(Integer),
    Underscore,
}

/// Fold an n-ary `=>` into the right-associative binary form the Lambdapi
/// encoding has: `(=> a b c)` becomes `a ⇒ (b ⇒ c)`.
///
/// SMT-LIB's `=>` is [`NaryCase::RightAssoc`](crate::ast::NaryCase), so the
/// arguments past the second are not decoration -- taking only `args[0]` and
/// `args[1]`, as this did, dropped them and emitted a hypothesis the problem
/// never asserted. This mirrors `expand_assoc` in the checker's `nary_elim`
/// (src/checker/rules/clausification.rs); keep the two in step.
///
/// Doing the unfolding here is also what makes `nary_elim` provable by
/// reflexivity in the backend: both sides of its equation become the same term.
fn nary_implies(args: Vec<Term>) -> Term {
    args.into_iter()
        .rev()
        .reduce(|acc, arg| Term::Alethe(LTerm::Implies(Box::new(arg), Box::new(acc))))
        .expect("`=>` has at least one argument")
}

/// Fold a chainable `=` into the conjunction of its adjacent pairs:
/// `(= a b c)` becomes `(a = b) ∧ (b = c)`. A two-argument `=` -- the common
/// case -- is unchanged. Matches the `Case::Chainable` branch of the checker's
/// `nary_elim`.
fn nary_equals(args: Vec<Term>) -> Term {
    if args.len() <= 2 {
        return Term::Alethe(LTerm::Eq(
            Box::new(args[0].clone()),
            Box::new(args[1].clone()),
        ));
    }
    Term::Alethe(LTerm::NAnd(
        args.windows(2)
            .map(|w| Term::Alethe(LTerm::Eq(Box::new(w[0].clone()), Box::new(w[1].clone()))))
            .collect_vec(),
    ))
}

/// The Lambdapi module a numeral is scoped against.
///
/// Decimal notation binds to one carrier at a time (Deducteam/lambdapi#1268) and
/// the binding belongs to whatever the file required last, so a bare `3` means ℕ
/// in a proof whose header stops at `alethe.core` and ℤ in one that also opens
/// `alethe.lia`. `Module.n` is lexed as a single token and scoped against that
/// module's own `builtin "0".."10"` table, so it means the same thing either way.
///
/// A real literal is `lit (n / d)`: `lit : ℚ → τ real` from `alethe.real`, over
/// the fraction `n / d` of `alethe.rat` with `n : ℤ` and `d : ℙ`. Both numerals
/// are module-scoped like the others; `Stdlib.Pos` binds `"+"`/`"*"` too, so a
/// denominator past ten assembles.
const NAT_MODULE: &str = "Stdlib.Nat";
const INT_MODULE: &str = "Stdlib.Z";
const POS_MODULE: &str = "Stdlib.Pos";

/// Render a ℕ literal. No `+1` counting past ten: the module's `"+"`/`"*"`
/// builtins assemble the digits.
pub(crate) fn nat_literal(n: u32) -> String {
    format!("{NAT_MODULE}.{n}")
}

/// Render a ℤ literal. `Integer`'s own `Display` writes the sign and `Stdlib.Z`
/// binds `builtin "-"`, so a negative literal is still one token and needs no
/// parentheses in argument position.
pub(crate) fn int_literal(i: &Integer) -> String {
    format!("{INT_MODULE}.{i}")
}

/// Render a ℙ literal. Only ever a denominator, so it is positive.
pub(crate) fn pos_literal(p: &Integer) -> String {
    format!("{POS_MODULE}.{p}")
}

/// Render a real literal. `rug` keeps the denominator positive, so the sign is
/// the numerator's and `/` from `alethe.rat` gets the `ℤ` and `ℙ` it expects.
pub(crate) fn real_literal(r: &Rational) -> String {
    format!("(lit ({} / {}))", int_literal(r.numer()), pos_literal(r.denom()))
}

#[macro_export]
macro_rules! underscore {
    () => {
        Term::Underscore
    };
}

#[macro_export]
macro_rules! terms {
    // Empty case
    () => {
        Term::Terms(vec![])
    };
    // Spread a vector: terms![..vec]
    (..$vec:expr) => {
        Term::Terms($vec)
    };
    // Single or multiple terms with optional spreading
    ($($t:tt)*) => {{
        let mut result = vec![];
        $crate::terms_internal!(result; $($t)*);
        Term::Terms(result)
    }};
}

#[macro_export]
#[doc(hidden)]
macro_rules! terms_internal {
    // Base case: nothing left
    ($result:ident;) => {};

    // Spread syntax: ..$vec
    ($result:ident; ..$vec:expr $(, $($rest:tt)*)?) => {
        $result.extend($vec);
        $crate::terms_internal!($result; $($($rest)*)?);
    };

    // Regular term
    ($result:ident; $t:expr $(, $($rest:tt)*)?) => {
        $result.extend([$t]);
        $crate::terms_internal!($result; $($($rest)*)?);
    };
}

#[cfg(test)]
mod tests_terms_macros {
    use super::*;

    #[test]
    fn test_terms_macro_empty() {
        let t = terms!();
        assert_eq!(t, Term::Terms(vec![]));
    }

    #[test]
    fn test_terms_macro_single() {
        let t = terms!(Term::Nat(1));
        assert_eq!(t, Term::Terms(vec![Term::Nat(1)]));
    }

    #[test]
    fn test_terms_macro_multiple() {
        let t = terms!(Term::Nat(1), Term::Nat(2), Term::Nat(3));
        assert_eq!(
            t,
            Term::Terms(vec![Term::Nat(1), Term::Nat(2), Term::Nat(3)])
        );
    }

    #[test]
    fn test_terms_macro_spread() {
        let vec_terms = vec![Term::Nat(1), Term::Nat(2)];
        let t = terms!(..vec_terms);
        assert_eq!(t, Term::Terms(vec![Term::Nat(1), Term::Nat(2)]));
    }

    #[test]
    fn test_terms_macro_mixed() {
        let vec_terms = vec![Term::Nat(2), Term::Nat(3)];
        let t = terms!(Term::Nat(1), ..vec_terms, Term::Nat(4));
        assert_eq!(
            t,
            Term::Terms(vec![Term::Nat(1), Term::Nat(2), Term::Nat(3), Term::Nat(4)])
        );
    }

    #[test]
    fn test_terms_macro_multiple_spreads() {
        let vec1 = vec![Term::Nat(1), Term::Nat(2)];
        let vec2 = vec![Term::Nat(4), Term::Nat(5)];
        let t = terms!(..vec1, Term::Nat(3), ..vec2);
        assert_eq!(
            t,
            Term::Terms(vec![
                Term::Nat(1),
                Term::Nat(2),
                Term::Nat(3),
                Term::Nat(4),
                Term::Nat(5)
            ])
        );
    }

    #[test]
    fn test_underscore_macro() {
        let t = underscore!();
        assert_eq!(t, Term::Underscore);
    }
}

/// This trait implements the visitor pattern for Lambdapi terms,
/// allowing systematic replacement of variables with their corresponding values
/// from a provided mapping.
pub trait VisitorArgs {
    /// Visits and potentially modifies a term by applying variable substitutions.
    fn visit(&mut self, mapping: &[(&SortedVar, &Rc<AletheTerm>)]);
}

impl VisitorArgs for LTerm {
    /// We implement the substitution perform by Alethe in subproof.
    /// Given an SMT term: `∀ x, (P(x) ∧ Q(y))` with an Alethe context Γ :=  [x → a, y → b].
    /// we then obtain `∀ x, (P(x) ∧ Q(b))`.
    /// Note that `x` is not substituted inside the `∀ x, ...` scope
    fn visit(&mut self, mapping: &[(&SortedVar, &Rc<AletheTerm>)]) {
        match self {
            // `List` and `Distinct` too: a `bind` over a bit-vector variable has
            // to reach the cells of a `bbterm`.
            LTerm::Clauses(ts)
            | LTerm::NOr(ts)
            | LTerm::NAnd(ts)
            | LTerm::List(List(ts))
            | LTerm::Distinct(VecN(ts)) => {
                ts.iter_mut().for_each(|t| t.visit(mapping));
            }
            LTerm::Choice(bs, t) => t.visit(
                // Keep only mappings for variables that are NOT bound by this Choice
                // `sbs.0`` in `filter` contains the bound variables, we exclude them from substitution
                &mapping
                    .iter()
                    .copied()
                    .filter(|((id, _ ), _)| bs.0.iter().any(|SortedTerm(bind_name, _)| matches!(bind_name.borrow(), Term::TermId(x) if x != id )))  // Keep the mapping if the bound variable name doesn't match the mapping id

                    .collect_vec()
            ),
            // Quantifiers (∃ and ∀) bind variables - similar filtering logic as Choice
            LTerm::Exist(Bindings(bs), t) | LTerm::Forall(Bindings(bs), t) => t.visit(
                &mapping
                    .iter()
                    .copied()
                    .filter(|((id, _), _)| bs.iter().any(|SortedTerm(bind_name, _)| matches!(bind_name.borrow(), Term::TermId(x) if x != id )))
                    .collect_vec()
            ),
            LTerm::Implies(t1, t2) | LTerm::Iff(t1, t2) | LTerm::Eq(t1, t2) => {
                t1.visit(mapping);
                t2.visit(mapping);
            }
            LTerm::Proof(t) => t.visit(mapping), // Proof wrapper - transparently visit the inner term
            LTerm::Neg(Some(t)) => t.visit(mapping),
            // Base case: for all other LTerm variants, no action needed
            // (likely literals or other constructs without subterms)
            _ => {}
        }
    }
}

impl VisitorArgs for Term {
    fn visit(&mut self, mapping: &[(&SortedVar, &Rc<AletheTerm>)]) {
        match self {
            Term::TermId(id) => {
                if let Some((_, t)) = mapping.iter().find(|((name, _), _)| id == name) {
                    *self = (*t).into();
                }
            }
            Term::Function(ts) | Term::Terms(ts) => {
                ts.iter_mut().for_each(|t| t.visit(mapping));
            }
            Term::Alethe(t) => t.visit(mapping),
            Term::Nat(_) | Term::Int(_) | Term::Real(_) | Term::Pos(_) => {}
            t => todo!("visitor {:?}", t),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::Alethe(t) => write!(f, "{}", t),
            Term::Sort(bs) => write!(f, "{}", bs),
            Term::TermId(id) => write!(f, "{}", id),
            Term::Function(terms) => write!(
                f,
                "{}",
                terms
                    .iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<_>>()
                    .join(" → ")
            ),
            Term::Terms(terms) => {
                write!(
                    f,
                    "( {} )",
                    terms
                        .iter()
                        .map(|x| format!("{}", x))
                        .collect::<Vec<_>>()
                        .join(WHITE_SPACE)
                )
            }
            Term::Nat(n) => write!(f, "{}", nat_literal(*n)),
            Term::Int(i) => write!(f, "{}", int_literal(i)),
            Term::Real(r) => write!(f, "{}", real_literal(r)),
            Term::Pos(p) => write!(f, "{}", pos_literal(p)),
            Term::Underscore => write!(f, "_"),
        }
    }
}

/// Use to translate the `cong` rule
/// An operator used as a value rather than applied: Lambdapi writes that as the
/// symbol between parentheses, `(=)`.
///
/// Built as a one-element application rather than the literal string `"(=)"` so that
/// `Term::TermId` only ever holds a bare identifier. The printer relies on that: it
/// escapes an identifier Lambdapi would reject, and `(=)` -- which is a parenthesised
/// term, not a name -- would come back out as `{|(=)|}`.
pub(crate) fn operator_section(name: &str) -> Term {
    Term::Terms(vec![Term::TermId(name.to_owned())])
}

impl Term {
    /// An operator used as a value, over the carrier `real` selects: the
    /// arithmetic symbols of `alethe.lra` are their own (`≤ᵣ`, `＋ᵣ`, …), since
    /// Lambdapi does not overload. `real` is read off the operands with
    /// [`any_real`].
    pub(crate) fn operator(op: Operator, real: bool) -> Term {
        let arith = |int: &str, re: &str| operator_section(if real { re } else { int });
        match op {
            Operator::Equals => operator_section("="),
            Operator::Or => operator_section("∨"),
            Operator::And => operator_section("∧"),
            Operator::LessEq => arith("≤", "≤ᵣ"),
            Operator::LessThan => arith("<", "<ᵣ"),
            Operator::Implies => operator_section("⇒"),
            Operator::Distinct => "distinct".into(),
            Operator::Add => arith("+", "＋ᵣ"),
            Operator::Mult => arith("*", "*ᵣ"),
            Operator::Sub => arith("-", "−ᵣ"),
            Operator::GreaterEq => arith("≥", "≥ᵣ"),
            Operator::GreaterThan => arith(">", ">ᵣ"),
            Operator::Not => operator_section("¬"),
            Operator::Ite => "ite".into(),
            Operator::Xor => "xor".into(),
            // A bit-vector operator is a plain prefix symbol of `alethe.bv`, so
            // it needs no section. `BvBbTerm` never reaches this: its congruence
            // goes through the list it carries (`rules::core::bbterm_cong`).
            o => match bv_op_name(o) {
                Some(name) => name.into(),
                None => todo!("Operator {:?}", o),
            },
        }
    }
}

impl From<Operator> for Term {
    fn from(op: Operator) -> Self {
        Term::operator(op, false)
    }
}

/// Is this term real-sorted? Read off the syntax, which is all the converters
/// have: a constant and a variable carry their sort, an application has its
/// function's, and an arithmetic operation is real as soon as one operand is.
pub(crate) fn is_real(term: &AletheTerm) -> bool {
    match term {
        AletheTerm::Const(c) => matches!(c, Constant::Real(_)),
        AletheTerm::Var(_, sort) => matches!(sort.deref(), Sort::Real),
        AletheTerm::App(f, _) => match f.deref() {
            AletheTerm::Var(_, sort) => match sort.deref() {
                Sort::Function(params) => {
                    params.last().is_some_and(|s| matches!(s.deref(), Sort::Real))
                }
                _ => false,
            },
            _ => false,
        },
        AletheTerm::Op(Operator::Ite, args) => args.iter().skip(1).any(|a| is_real(a)),
        AletheTerm::Op(Operator::Add | Operator::Sub | Operator::Mult, args) => any_real(args),
        _ => false,
    }
}

/// Does any of these operands make the operation real?
pub(crate) fn any_real(args: &[Rc<AletheTerm>]) -> bool {
    args.iter().any(|a| is_real(a))
}

/// An integer literal where a real is expected (`--allow-int-real-subtyping`)
/// has to be a real literal in Lambdapi.
fn as_real(term: Term) -> Term {
    match term {
        Term::Int(i) => Term::Real(Rational::from(i)),
        t => t,
    }
}

/// The arguments of `f` applied, with integer literals coerced where `f` takes
/// a real: `(f 0)` for `f : Real → …`.
fn coerce_real_args(f: &AletheTerm, args: Vec<Term>) -> Vec<Term> {
    let AletheTerm::Var(_, sort) = f else { return args };
    let Sort::Function(params) = sort.deref() else { return args };
    params
        .iter()
        .zip(args)
        .map(|(param, arg)| if matches!(param.deref(), Sort::Real) { as_real(arg) } else { arg })
        .collect()
}

/// An arithmetic operation over the carrier `real` selects (see
/// [`Term::operator`]). The n-ary `+`, `-` and `*` are interspersed, which the
/// right-associative infix notations of both carriers read as SMT-LIB does.
fn arith_term(op: Operator, args: Vec<Term>, real: bool) -> Term {
    let args = if real { args.into_iter().map(as_real).collect_vec() } else { args };
    let sym = |int: &str, re: &str| Term::from(if real { re } else { int });
    let infix = |args: Vec<Term>, s: Term| Term::Terms(itertools::intersperse(args, s).collect_vec());
    match op {
        Operator::Sub if args.len() == 1 => Term::Terms(vec![sym("—", "—ᵣ"), args[0].clone()]),
        Operator::Sub => infix(args, sym("-", "−ᵣ")),
        Operator::Add => infix(args, sym("+", "＋ᵣ")),
        Operator::Mult => infix(args, sym("*", "*ᵣ")),
        Operator::GreaterEq => Term::Terms(vec![args[0].clone(), sym("≥", "≥ᵣ"), args[1].clone()]),
        Operator::GreaterThan => Term::Terms(vec![args[0].clone(), sym(">", ">ᵣ"), args[1].clone()]),
        Operator::LessEq => Term::Terms(vec![args[0].clone(), sym("≤", "≤ᵣ"), args[1].clone()]),
        Operator::LessThan => Term::Terms(vec![args[0].clone(), sym("<", "<ᵣ"), args[1].clone()]),
        o => unreachable!("not an arithmetic operator: {o:?}"),
    }
}

impl<S: Into<String>> From<S> for Term {
    fn from(id: S) -> Self {
        Term::TermId(id.into())
    }
}

/// Converts an Alethe term to a Lambdapi term and collects shared variables (occurrences of a subexpression exceeds the value set by `dag-thresh` in cvc5).
///
/// The `HashSet` of shared terms is crucial for Lambdapi proof steps because it tells us
/// which terms can be unfolded (`simplify`) (expanded to their definitions) during proof construction.
///
/// # Parameters
/// * `term` - The Alethe term to convert
/// * `ctx` - The context containing term sharing information
///
/// # Returns
/// A tuple containing:
/// * `Term` - The converted Lambdapi term
/// * `HashSet<Term>` - Collection of shared variables found during conversion.
///
pub fn conv(
    term: &Rc<AletheTerm>,
    ctx: &crate::translation::lambdapi::Context,
) -> (Term, HashSet<String>) {
    /// Auxiliary function of `conv` above that performs the actual conversion work recursively with the shared variables passed in parameter.
    fn conv_aux(
        term: &Rc<AletheTerm>,
        ctx: &crate::translation::lambdapi::Context,
        shared_var: &mut HashSet<String>,
    ) -> Term {
        // Check if this term is in the shared terms dictionary
        if let Some((name, _def)) = ctx.term_sharing.get(term) {
            shared_var.insert(name.into());
            Term::from(name)
        } else {
            // Not a shared term - perform direct conversion
            match term.deref() {
                AletheTerm::App(f, args) => {
                    // Function applications: convert function and arguments separately

                    let mut func = vec![conv(f, ctx).0];
                    let args: Vec<Term> =
                        args.iter().map(|a| conv_aux(a, ctx, shared_var)).collect();
                    func.extend(coerce_real_args(f, args));
                    Term::Terms(func)
                }
                AletheTerm::Op(operator, args) => {
                    let real = any_real(args);
                    let alethe_args = args;
                    let args = args
                        .iter()
                        .map(|a| conv_aux(a, ctx, shared_var))
                        .collect::<VecDeque<_>>();
                    match operator {
                        Operator::Not => {
                            Term::Alethe(LTerm::Neg(Some(Box::new(args.front().cloned().unwrap()))))
                        }
                        Operator::Or => Term::Alethe(LTerm::NOr(args.into())),
                        Operator::Equals => nary_equals(args.into()),
                        Operator::And => Term::Alethe(LTerm::NAnd(args.into())),
                        Operator::Implies => nary_implies(args.into()),
                        Operator::Distinct => {
                            Term::Alethe(LTerm::Distinct(VecN(args.into_iter().collect_vec())))
                        }
                        Operator::Sub
                        | Operator::Add
                        | Operator::Mult
                        | Operator::GreaterEq
                        | Operator::GreaterThan
                        | Operator::LessEq
                        | Operator::LessThan => arith_term(*operator, args.into(), real),
                        Operator::RareList => Term::Terms(args.into_iter().collect_vec()),
                        // SMT-LIB `xor` is left-associative.
                        Operator::Xor => args
                            .into_iter()
                            .reduce(|acc, arg| Term::Terms(vec![Term::from("xor"), acc, arg]))
                            .expect("xor takes at least two arguments"),
                        Operator::True => Term::Alethe(LTerm::True),
                        Operator::False => Term::Alethe(LTerm::False),
                        Operator::Ite => Term::Terms(vec![
                            Term::from("ite".to_owned()),
                            args[0].clone(),
                            args[1].clone(),
                            args[2].clone(),
                        ]),
                        // `alethe.bvint`'s ℤ helpers (cvc5 uses them around bit-vectors).
                        Operator::Mod => Term::Terms(vec![Term::from("Zmod"), args[0].clone(), args[1].clone()]),
                        Operator::Pow2 => Term::Terms(vec![Term::from("Zpow2"), args[0].clone()]),
                        o => bv_op(*o, alethe_args, args.into())
                            .unwrap_or_else(|| todo!("Operator {:?}", o)),
                    }
                }
                AletheTerm::ParamOp { op, op_args, args } => {
                    let args = args.iter().map(|a| conv_aux(a, ctx, shared_var)).collect();
                    param_op(*op, op_args, args)
                        .unwrap_or_else(|| todo!("indexed operator {:?} {:?}", op, op_args))
                }
                AletheTerm::Let(..) => todo!("let term"),
                AletheTerm::Binder(AletheBinder::Forall, bs, t) => Term::Alethe(LTerm::Forall(
                    Bindings::from(bs),
                    Box::new(conv_aux(t, ctx, shared_var)),
                )),
                AletheTerm::Binder(AletheBinder::Exists, bs, t) => Term::Alethe(LTerm::Exist(
                    Bindings::from(bs),
                    Box::new(conv_aux(t, ctx, shared_var)),
                )),
                AletheTerm::Binder(AletheBinder::Choice, bs, t) => Term::Alethe(LTerm::Choice(
                    Bindings::from(bs),
                    Box::new(conv_aux(t, ctx, shared_var)),
                )),
                AletheTerm::Var(id, _term) => Term::TermId(id.clone()),
                AletheTerm::Const(c) => match c {
                    Constant::Integer(i) => Term::Int(i.clone()),
                    Constant::Real(r) => Term::Real(r.clone()),
                    Constant::String(s) => Term::from(s),
                    Constant::BitVec(v, w) => bv_literal(v, *w),
                    c @ Constant::RegLan(..) => unimplemented!("Constant {}", c),
                },
                e => todo!("{:#?}", e),
            }
        }
    }

    let mut shared_var: HashSet<_> = HashSet::new();
    let t = conv_aux(term, ctx, &mut shared_var);
    (t, shared_var)
}

impl From<&Rc<AletheTerm>> for Term {
    fn from(term: &Rc<AletheTerm>) -> Self {
        Term::from(term.deref().clone())
    }
}

impl From<Rc<AletheTerm>> for Term {
    fn from(term: Rc<AletheTerm>) -> Self {
        Self::from(&term)
    }
}

impl From<&Sort> for Term {
    fn from(sort: &Sort) -> Self {
        match sort {
            Sort::Function(params) => Term::Function(params.iter().map(Term::from).collect()),
            Sort::Atom(id, _sorts) => Term::TermId(id.to_string()),
            Sort::Bool => Term::Sort(BuiltinSort::Bool),
            Sort::Int => Term::Sort(BuiltinSort::Int),
            Sort::Real => Term::Sort(BuiltinSort::Real),
            Sort::BitVec(n) => bitvec_sort(*n),
            s => todo!("{:#?}", s),
        }
    }
}

impl From<&Rc<Sort>> for Term {
    fn from(sort: &Rc<Sort>) -> Self {
        Term::from(sort.deref())
    }
}

impl From<AletheTerm> for Term {
    fn from(term: AletheTerm) -> Self {
        match term {
            AletheTerm::App(f, args) => {
                let args: Vec<Term> = args.into_iter().map(Term::from).collect();
                let mut func = vec![Term::from(&f)];
                func.extend(coerce_real_args(&f, args));
                Term::Terms(func)
            }
            AletheTerm::Op(operator, alethe_args) => {
                let real = any_real(&alethe_args);
                let args = alethe_args.iter().map(Term::from).collect::<VecDeque<_>>();
                match operator {
                    Operator::Not => {
                        Term::Alethe(LTerm::Neg(Some(Box::new(args.front().cloned().unwrap()))))
                    }
                    Operator::Or => {
                        //args.push_back(Term::Alethe(LTerm::False));
                        Term::Alethe(LTerm::NOr(args.into()))
                    }
                    Operator::Equals => nary_equals(args.into()),
                    Operator::And => {
                        //args.push_back(Term::Alethe(LTerm::True));
                        Term::Alethe(LTerm::NAnd(args.into()))
                    }
                    Operator::Implies => nary_implies(args.into()),
                    Operator::Distinct => {
                        Term::Alethe(LTerm::Distinct(VecN(args.into_iter().collect_vec())))
                    }
                    Operator::Sub
                    | Operator::Add
                    | Operator::Mult
                    | Operator::GreaterEq
                    | Operator::GreaterThan
                    | Operator::LessEq
                    | Operator::LessThan => arith_term(operator, args.into(), real),
                    Operator::RareList => Term::Terms(args.into_iter().collect_vec()),
                    // SMT-LIB `xor` is left-associative.
                    Operator::Xor => args
                        .into_iter()
                        .reduce(|acc, arg| Term::Terms(vec![Term::from("xor"), acc, arg]))
                        .expect("xor takes at least two arguments"),
                    Operator::True => Term::Alethe(LTerm::True),
                    Operator::False => Term::Alethe(LTerm::False),
                    Operator::Ite => Term::Terms(vec![
                        Term::from("ite".to_owned()),
                        args[0].clone(),
                        args[1].clone(),
                        args[2].clone(),
                    ]),
                    Operator::Mod => Term::Terms(vec![Term::from("Zmod"), args[0].clone(), args[1].clone()]),
                    Operator::Pow2 => Term::Terms(vec![Term::from("Zpow2"), args[0].clone()]),
                    o => bv_op(o, &alethe_args, args.into())
                        .unwrap_or_else(|| todo!("Operator {:?}", o)),
                }
            }
            AletheTerm::ParamOp { op, op_args, args } => {
                let args = args.iter().map(Term::from).collect();
                param_op(op, &op_args, args)
                    .unwrap_or_else(|| todo!("indexed operator {:?} {:?}", op, op_args))
            }
            AletheTerm::Let(..) => todo!("let term"),
            AletheTerm::Binder(AletheBinder::Forall, bs, t) => {
                Term::Alethe(LTerm::Forall(Bindings::from(bs), Box::new(Term::from(t))))
            }
            AletheTerm::Binder(AletheBinder::Exists, bs, t) => {
                Term::Alethe(LTerm::Exist(Bindings::from(bs), Box::new(Term::from(t))))
            }
            AletheTerm::Binder(AletheBinder::Choice, bs, t) => {
                Term::Alethe(LTerm::Choice(Bindings::from(bs), Box::new(Term::from(t))))
            }
            AletheTerm::Var(id, _term) => Term::TermId(id),
            AletheTerm::Const(c) => match c {
                Constant::Integer(i) => Term::Int(i.clone()),
                Constant::Real(r) => Term::Real(r),
                Constant::String(s) => Term::from(s),
                Constant::BitVec(v, w) => bv_literal(&v, w),
                c @ Constant::RegLan(..) => unimplemented!("Constant {}", c),
            },
            e => todo!("{:#?}", e),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Param(pub String, pub Term);

impl fmt::Display for Param {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Param(id, _term) => write!(f, "{}", id),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SortedTerm(pub Box<Term>, pub Box<Term>);

impl From<&SortedVar> for SortedTerm {
    fn from(var: &SortedVar) -> Self {
        SortedTerm(
            Box::new(Term::TermId(var.0.clone())),
            Box::new(tau(Term::from(&var.1))),
        )
    }
}

impl fmt::Display for SortedTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.0, self.1)
    }
}

/// Represent the Stdlib.List inductive type in a shallow Rust encoding (Vec).
/// This structure exists for making pretty printing easier by not overloading `LTerm`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Bindings(pub Vec<SortedTerm>);

impl From<&BindingList> for Bindings {
    fn from(bindings: &BindingList) -> Self {
        Bindings(
            bindings
                .into_iter()
                .map(SortedTerm::from)
                .collect::<Vec<_>>(),
        )
    }
}

impl From<BindingList> for Bindings {
    fn from(bindings: BindingList) -> Self {
        Bindings(
            bindings
                .into_iter()
                .map(SortedTerm::from)
                .collect::<Vec<_>>(),
        )
    }
}

impl fmt::Display for Bindings {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = Itertools::intersperse(
            self.0.iter().map(|t| format!("({})", t)),
            WHITE_SPACE.to_owned(),
        )
        .collect::<String>();
        write!(f, "{}", s)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VecN(pub Vec<Term>);

impl fmt::Display for VecN {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = self
            .0
            .iter()
            .rev()
            .fold("⧈".to_owned(), |acc, e| format!("(cons {} {})", e, acc));
        write!(f, "{}", s)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct List(pub Vec<Term>);

impl fmt::Display for List {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = self
            .0
            .iter()
            .rev()
            .fold("□".to_owned(), |acc, e| format!("{} ⸬ {}", e, acc));
        write!(f, "{}", s)
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum LTerm {
    True,
    False,
    NAnd(Vec<Term>),
    NOr(Vec<Term>),
    Neg(Option<Box<Term>>), //TODO: explain why cong need to add Option to Neg
    Implies(Box<Term>, Box<Term>),
    Iff(Box<Term>, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    Clauses(Vec<Term>),
    ClassicProof(Box<Term>),
    Proof(Box<Term>),
    Forall(Bindings, Box<Term>),
    Exist(Bindings, Box<Term>),
    Distinct(VecN),
    List(List),
    Choice(Bindings, Box<Term>),
}

#[cfg(test)]
pub(crate) mod test_macros {
    use crate::translation::lambdapi::syntax::printer::PrettyPrint;
    use crate::translation::lambdapi::{
        Command, Config, ProofFile, TradResult, produce_lambdapi_proof,
    };

    /// Parses an inline problem/proof pair with the current upstream parser API.
    pub fn parse_test_instance(
        problem: &str,
        proof: &str,
    ) -> crate::CarcaraResult<(
        crate::ast::Problem,
        crate::ast::Proof,
        crate::ast::rare_rules::Rules,
        crate::ast::pool::PrimitivePool,
    )> {
        crate::parser::parse_instance(
            crate::parser::Source::new(std::path::Path::new("test.smt2"), problem),
            crate::parser::Source::new(std::path::Path::new("test.alethe"), proof),
            None,
            crate::parser::Config::new(),
        )
    }

    /// Translate an inline problem/proof pair end to end, as the CLI does.
    pub fn translate(problem: &str, proof: &str, config: Config) -> TradResult<ProofFile> {
        let (problem, proof, _, pool) = parse_test_instance(problem, proof).unwrap();
        produce_lambdapi_proof(problem.prelude, proof, pool, config)
    }

    /// The `require` header of a translated proof, as module paths.
    pub fn requires_of(problem: &str, proof: &str) -> Vec<String> {
        translate(problem, proof, Config::default())
            .expect("translation failed")
            .requires
            .iter()
            .map(|c| match c {
                Command::RequireOpen(m) => m.clone(),
                other => panic!("not a require: {other:?}"),
            })
            .collect()
    }

    /// The commands of a translated proof, after the header and the declarations.
    pub fn content_of(problem: &str, proof: &str) -> Vec<Command> {
        translate(problem, proof, Config::default())
            .expect("translation failed")
            .content
    }

    /// The generated file as the CLI prints it, its whitespace collapsed so a
    /// test can look for a script regardless of line breaks.
    pub fn printed_with(problem: &str, proof: &str, config: Config) -> String {
        let file = translate(problem, proof, config).expect("translation failed");
        file.to_pretty()
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// [`printed_with`] under the default configuration.
    pub fn printed(problem: &str, proof: &str) -> String {
        printed_with(problem, proof, Config::default())
    }

    macro_rules! cl {
        ($($x:expr),+ $(,)?) => {
            Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses( vec![ $($x),+ ] )))))
        };
    }

    macro_rules! id {
        ($x1:expr) => {
            Term::TermId($x1.into())
        };
    }

    macro_rules! bid {
        ($x1:expr) => {
            Term::TermId($x1.into())
        };
    }

    macro_rules! not {
        ($x1:expr) => {
            Term::Alethe(LTerm::Neg(Some(Box::new($x1))))
        };
    }

    macro_rules! eq {
        ($x1:expr, $x2:expr) => {
            Term::Alethe(LTerm::Eq(Box::new($x1), Box::new($x2)))
        };
    }

    macro_rules! imp {
        ($x1:expr, $x2:expr) => {
            Term::Alethe(LTerm::Implies(Box::new($x1), Box::new($x2)))
        };
    }

    macro_rules! or {
        ($($x:expr),+ $(,)?) => {
            Term::Alethe(LTerm::NOr(vec![
                $($x),+
            ]))
        };
    }

    macro_rules! and {
        ($($x:expr),+ $(,)?) => {
            Term::Alethe(LTerm::NAnd(vec![
                $($x),+
            ]))
        };
    }

    pub(crate) use {and, bid, cl, eq, id, imp, not, or};
}

impl fmt::Display for LTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LTerm::True => write!(f, "⊤"),
            LTerm::False => write!(f, "⊥"),
            LTerm::Neg(Some(t)) => write!(f, "(¬ {})", t),
            LTerm::Neg(None) => write!(f, "¬"),
            LTerm::NAnd(ts) => {
                let s =
                    Itertools::intersperse(ts.iter().map(|t| format!("{}", t)), " ∧ ".to_owned())
                        .collect::<String>();
                write!(f, "{}", s)
            }
            LTerm::NOr(ts) => {
                let s =
                    Itertools::intersperse(ts.iter().map(|t| format!("{}", t)), " ∨ ".to_owned())
                        .collect::<String>();
                write!(f, "{}", s)
            }
            LTerm::Clauses(ts) => {
                // Same encoding as the doc printer: a clause is a `𝕃 o`, so even
                // the empty one is `□` and every other ends in `⸬ □`.
                for t in ts {
                    write!(f, "({}) ⸬ ", t)?;
                }
                write!(f, "□")
            }
            LTerm::Implies(l, r) => {
                write!(f, "({}) ⇒ ({})", l, r)
            }
            LTerm::Iff(l, r) => {
                write!(f, "({}) ⇔ ({})", l, r)
            }
            LTerm::Eq(l, r) => {
                write!(f, "({}) = ({})", l, r)
            }
            LTerm::Proof(t) => write!(f, "π ({})", t),
            LTerm::ClassicProof(t) => write!(f, "π ({})", t),
            LTerm::Forall(bs, t) => write!(f, "`∀ {}, {}", bs, t),
            LTerm::Exist(bs, t) => write!(f, "`∃ {}, {}", bs, t),
            LTerm::Distinct(l) => write!(f, "distinct ({})", l),
            LTerm::List(l) => write!(f, "({})", l),
            LTerm::Choice(x, p) => write!(f, "`ϵ {}, {}", x, p),
        }
    }
}

#[inline]
pub fn clauses(terms: Vec<Term>) -> Term {
    Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(terms)))))
}

pub trait Visitor {
    fn visit(&self, ctx: &mut Context, pool: &mut PrimitivePool);
}

impl Visitor for Rc<AletheTerm> {
    fn visit(&self, ctx: &mut Context, pool: &mut PrimitivePool) {
        match self.deref() {
            AletheTerm::Const(_)
            | AletheTerm::Var(..)
            | AletheTerm::Match(..)
            | AletheTerm::AsOp(..)
            | AletheTerm::ParamOp { .. }
            | AletheTerm::Let(..)
            | AletheTerm::Op(Operator::True | Operator::False, _) => {}
            AletheTerm::Op(_, ops) => {
                if self.is_closed(pool, &ctx.global_variables) {
                    if let Some((count, t)) = ctx.term_indices.get_mut(self) {
                        *count += 1;
                        if *count >= 1 {
                            ctx.term_sharing
                                .insert(self.clone(), ((*t).clone(), self.into()));
                        }
                    } else {
                        ctx.term_indices.insert(
                            self.clone(),
                            (1, format!("p_{}", ctx.term_indices.len() + 1)),
                        );
                    }
                }
                ops.iter().for_each(|op| op.visit(ctx, pool));
            }
            AletheTerm::App(o, ops) => {
                if self.is_closed(pool, &ctx.global_variables) {
                    if let Some((count, t)) = ctx.term_indices.get_mut(self) {
                        *count += 1;
                        if *count >= 1 {
                            ctx.term_sharing
                                .insert(self.clone(), ((*t).clone(), self.into()));
                        }
                    } else {
                        ctx.term_indices.insert(
                            self.clone(),
                            (1, format!("p_{}", ctx.term_indices.len() + 1)),
                        );
                    }
                }
                o.visit(ctx, pool);
                ops.iter().for_each(|op| op.visit(ctx, pool));
            }
            AletheTerm::Binder(_, bs, t) => {
                let bounded_variables = bs.into_iter().map(|(name, _)| name).collect_vec();
                let free_vars_remaining = pool
                    .free_vars(self)
                    .into_owned()
                    .into_iter()
                    .filter(|var| !ctx.global_variables.contains(var))
                    .filter(|var| match var.deref() {
                        AletheTerm::Var(var, _) => !bounded_variables.contains(&var),
                        _ => false,
                    })
                    .collect_vec();

                if free_vars_remaining.is_empty() {
                    if let Some((count, t)) = ctx.term_indices.get_mut(self) {
                        *count += 1;
                        if *count >= 1 {
                            ctx.term_sharing
                                .insert(self.clone(), ((*t).clone(), self.into()));
                        }
                    } else {
                        ctx.term_indices.insert(
                            self.clone(),
                            (1, format!("p_{}", ctx.term_indices.len() + 1)),
                        );
                    }
                }
                t.visit(ctx, pool);
            }
        }
    }
}

#[cfg(test)]
mod tests_term {
    use super::test_macros::parse_test_instance;
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn test_free_var_collection() {
        let problem = "
            (declare-sort Idv 0)
            (declare-fun clt () Idv)
            (declare-fun cap (Idv Idv) Idv)
            (declare-fun FunApp (Idv Idv) Idv)
            (declare-fun FunExcept (Idv Idv Idv) Idv)
            (declare-fun Mem (Idv Idv) Bool)
            (declare-fun SetEnum () Idv)
            (declare-fun TrigEq (Idv Idv) Bool)
            (declare-fun TrigEqDollar (Idv
            Idv) Bool)
            (declare-fun Client () Idv)
            (declare-fun Res () Idv)
            (declare-fun VarUnsat () Idv)
            (declare-fun UnsatPrim () Idv)
            (declare-fun Alloc () Idv)
            (declare-fun AllocPrim () Idv)
            (declare-fun S () Idv)
        ";
        let proof = "
            (assume Goal (! (not (=> (! (and (forall ((c1 Idv) (c2 Idv)) (=> (and (Mem c1 Client) (Mem c2 Client)) (forall ((r Idv)) (=> (Mem r Res) (=> (Mem r (cap (FunApp Alloc c1) (FunApp Alloc c2))) (TrigEq c1 c2)))))) (and (and (! (TrigEqDollar (FunApp VarUnsat clt) SetEnum) :named @p_5) (! (TrigEqDollar (FunApp Alloc clt) SetEnum) :named @p_4)) (and (! (not (TrigEqDollar S SetEnum)) :named @p_3) (! (TrigEq UnsatPrim (FunExcept VarUnsat clt S)) :named @p_2)) (! (TrigEq AllocPrim Alloc) :named @p_1))) :named @p_6) (forall ((c1 Idv) (c2 Idv)) (=> (and (Mem c1 Client) (Mem c2 Client)) (forall ((r Idv)) (=> (Mem r Res) (=> (Mem r (cap (FunApp AllocPrim c1) (FunApp AllocPrim c2))) (TrigEq c1 c2)))))))) :named @p_7))
            (step t1 (cl (and (Mem S S) (not (=> (! (and (forall ((c1 Idv) (c2 Idv)) (=> (and (Mem c1 Client) (Mem c2 Client)) (forall ((r Idv)) (=> (Mem r Res) (=> (Mem r (cap (FunApp Alloc c1) (FunApp Alloc c2))) (TrigEq c1 c2)))))) (and (and (! (TrigEqDollar (FunApp VarUnsat clt) SetEnum) :named @p_5) (! (TrigEqDollar (FunApp Alloc clt) SetEnum) :named @p_4)) (and (! (not (TrigEqDollar S SetEnum)) :named @p_3) (! (TrigEq UnsatPrim (FunExcept VarUnsat clt S)) :named @p_2)) (! (TrigEq AllocPrim Alloc) :named @p_1))) :named @p_6) (forall ((c1 Idv) (c2 Idv)) (=> (and (Mem c1 Client) (Mem c2 Client)) (forall ((r Idv)) (=> (Mem r Res) (=> (Mem r (cap (FunApp AllocPrim c1) (FunApp AllocPrim c2))) (TrigEq c1 c2))))))))))  :rule hole)
        ";
        let (problem, proof, _, mut pool) = parse_test_instance(problem, proof).unwrap();

        let mut ctx = Context::default();

        let global_variables: HashSet<_> = problem
            .prelude
            .function_declarations
            .iter()
            .map(|var| pool.add(var.clone().into()))
            .collect();

        ctx.global_variables = global_variables;

        let res = crate::translation::lambdapi::translate_commands(
            &mut ctx,
            &mut proof.iter(),
            &mut pool,
            &crate::translation::lambdapi::Config::default(),
            &mut crate::translation::lambdapi::logic::Features::EMPTY,
            |id, t, ps| {
                Command::Symbol(
                    None,
                    crate::translation::lambdapi::normalize_name(id),
                    vec![],
                    t,
                    ps.map(Proof),
                )
            },
        )
        .expect("translate cong");

        assert_eq!(2, res.len());
    }

    #[test]
    fn test_free_var_quantifier() {
        let problem = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ";
        let proof = "
            (step t1 (cl (or
                    (not (forall ((p Bool) (q Bool))
                        (not (and (=> p q) (or q (not (not p))) (or r false (not q))))
                    ))
                    (forall ((p Bool) (q Bool)) (or p (not q) (not s)))
                )) :rule qnt_cnf)
        ";
        let (problem, proof, _, mut pool) = parse_test_instance(problem, proof).unwrap();

        let global_variables: HashSet<_> = problem
            .prelude
            .function_declarations
            .iter()
            .map(|var| pool.add(var.clone().into()))
            .collect();

        assert_eq!(1, proof.commands.len());

        let forest = crate::ast::ProofNodeForest::from_commands(proof.commands.clone());
        let node = forest.0.last().unwrap();

        let clause = node.clause().first().unwrap();

        let mut ctx = Context {
            global_variables,
            ..Default::default()
        };

        clause.visit(&mut ctx, &mut pool);
    }

    use crate::ast::pool::{PrimitivePool, TermPool};
    use crate::parser::tests::parse_terms;

    fn conv_term(definitions: &str, term: &str) -> Rc<AletheTerm> {
        let mut pool = PrimitivePool::new();
        let [t] = parse_terms(&mut pool, definitions, [term]);
        t
    }

    #[test]
    fn test_arith() {
        let definitions = "
            (declare-sort Idv 0)
            (declare-fun CONSTANT_i_ () Idv)
            (declare-fun TLA_Proj_Int (Idv) Int)
        ";
        let t = "(= (>= (+ 1 (* -1 (TLA_Proj_Int CONSTANT_i_))) 1) (<= (- (+ 1 (* -1 (TLA_Proj_Int CONSTANT_i_)))) (- 1))))";
        let tp: Term = conv_term(definitions, t).into();
        println!("{}", tp);
    }

    use crate::translation::lambdapi::syntax::printer::PrettyPrint;

    const BV_DEFS: &str = "
        (declare-fun a () (_ BitVec 4))
        (declare-fun b () (_ BitVec 4))
        (declare-fun c () (_ BitVec 4))
        (declare-fun p () Bool)
        (declare-fun q () Bool)
    ";

    /// `term` through both converters -- `conv`, which the steps use, and
    /// `From<AletheTerm>`, which the shared-term definitions use -- which must
    /// agree; pretty-printed as the CLI prints it.
    fn converted(term: &str) -> String {
        let t = conv_term(BV_DEFS, term);
        let by_conv = conv(&t, &Context::default()).0.to_pretty();
        let by_from = Term::from(&t).to_pretty();
        assert_eq!(by_conv, by_from, "the two converters disagree on {term}");
        by_conv
    }

    #[test]
    fn a_bitvec_sort_prints_as_bitvec_nat() {
        assert_eq!(
            Term::from(&Sort::BitVec(8)).to_pretty(),
            "(bitvec Stdlib.Nat.8)"
        );
        assert_eq!(
            tau(bitvec_sort(1)).to_pretty(),
            "(τ ((bitvec Stdlib.Nat.1)))"
        );
        // Through a binder's sort annotation.
        assert_eq!(
            converted("(forall ((v (_ BitVec 2))) (= v v))"),
            "(`∀ (v : (τ ((bitvec Stdlib.Nat.2)))), (v = v))"
        );
    }

    /// `#b0110` and `(_ bv6 4)` are the same constant and print as the same
    /// digit list, least significant bit first.
    #[test]
    fn a_bitvec_literal_is_an_lsb_first_digit_list() {
        let six = "(bvlit Stdlib.Nat.4 (false ⸬ true ⸬ true ⸬ false ⸬ □))";
        assert_eq!(converted("#b0110"), six);
        assert_eq!(converted("(_ bv6 4)"), six);
        assert_eq!(converted("#b1"), "(bvlit Stdlib.Nat.1 (true ⸬ □))");
        // Leading zeros are digits too: the width is the sort's.
        assert_eq!(
            converted("(_ bv1 3)"),
            "(bvlit Stdlib.Nat.3 (true ⸬ false ⸬ false ⸬ □))"
        );
    }

    #[test]
    fn nary_bv_ops_fold_left() {
        assert_eq!(converted("(bvadd a b c)"), "(bvadd (bvadd a b) c)");
        assert_eq!(converted("(bvand a b c)"), "(bvand (bvand a b) c)");
        // `concat`'s last argument is the low part; the fold keeps the order.
        assert_eq!(converted("(concat a b c)"), "(concat (concat a b) c)");
        assert_eq!(converted("(bvadd a b)"), "(bvadd a b)");
        // Binary and unary operators are plain prefix applications.
        assert_eq!(converted("(bvsub a b)"), "(bvsub a b)");
        assert_eq!(converted("(bvult a b)"), "(bvult a b)");
        assert_eq!(converted("(bvnot (bvneg a))"), "(bvnot (bvneg a))");
    }

    #[test]
    fn indexed_ops_take_nat_indices() {
        assert_eq!(
            converted("((_ extract 2 1) a)"),
            "(extract Stdlib.Nat.2 Stdlib.Nat.1 a)"
        );
        assert_eq!(converted("((_ @bit_of 3) a)"), "(bit_of Stdlib.Nat.3 a)");
        assert_eq!(
            converted("((_ zero_extend 4) a)"),
            "(zero_extend Stdlib.Nat.4 a)"
        );
        assert_eq!(
            converted("((_ sign_extend 4) a)"),
            "(sign_extend Stdlib.Nat.4 a)"
        );
        assert_eq!(
            converted("((_ extract 3 2) (concat a b))"),
            "(extract Stdlib.Nat.3 Stdlib.Nat.2 (concat a b))"
        );
    }

    #[test]
    fn bbterm_is_an_arity_and_a_list() {
        assert_eq!(
            converted("(@bbterm p q)"),
            "(bbterm Stdlib.Nat.2 (p ⸬ q ⸬ □))"
        );
        assert_eq!(
            converted("(@bbterm ((_ @bit_of 0) a) ((_ @bit_of 1) a))"),
            "(bbterm Stdlib.Nat.2 ((bit_of Stdlib.Nat.0 a) ⸬ (bit_of Stdlib.Nat.1 a) ⸬ □))"
        );
        assert_eq!(converted("(@bbterm true)"), "(bbterm Stdlib.Nat.1 (⊤ ⸬ □))");
        assert_eq!(
            converted("(@bbterm (and p q) (not p))"),
            "(bbterm Stdlib.Nat.2 ((p ∧ q) ⸬ (¬ (p)) ⸬ □))"
        );
    }

    /// cvc5's `@bv v w` with numeral arguments is the literal `(_ bvv w)` denotes,
    /// so it never names a ℤ numeral; `@bvsize` is `alethe.bv`'s `bvsize`.
    #[test]
    fn bv_const_with_numerals_is_a_literal() {
        assert_eq!(converted("(@bv 6 4)"), converted("#b0110"));
        assert_eq!(
            converted("(@bv 0 2)"),
            "(bvlit Stdlib.Nat.2 (false ⸬ false ⸬ □))"
        );
        assert_eq!(converted("(@bvsize a)"), "(bvsize a)");
    }

    /// A `bind` substitution has to reach inside a `bbterm`'s list: the
    /// substituted clauses of the subproof's steps are what Lambdapi sees.
    #[test]
    fn a_bind_over_a_bitvector_substitutes_inside_bbterm() {
        let mut pool = PrimitivePool::new();
        let [t, y] = parse_terms(
            &mut pool,
            "(declare-fun x () (_ BitVec 1)) (declare-fun y () (_ BitVec 1))",
            [
                "(and (= (@bbterm ((_ @bit_of 0) x)) x) (distinct x x))",
                "y",
            ],
        );
        let mut lp = Term::from(&t);
        let x: SortedVar = ("x".to_owned(), pool.sort(&y));
        lp.visit(&[(&x, &y)]);
        assert_eq!(
            lp.to_pretty(),
            "(((bbterm Stdlib.Nat.1 ((bit_of Stdlib.Nat.0 y) ⸬ □)) = y) ∧ (distinct(cons y (cons y ⧈))))"
        );
    }
}

#[inline]
pub fn intro_top() -> Term {
    Term::from("⊤ᵢ")
}
