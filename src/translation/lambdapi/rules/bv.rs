//! cvc5's bit-vector rules: the bit-blasting steps `bv_bitblast_step_*`,
//! `bv_bitwise_slicing`, and the structural RARE rewrites (`bv-concat-extract-merge`,
//! `bv-extract-concat-*`, …). Mirrors `alethe-lp/bv.lp`.
//!
//! Two kinds of scripts:
//!
//! - **One lemma per rule** for the bit-blasting of an operation on
//!   `@bbterm`s (`bb_var`, `bb_equal`, `bb_add`, `bb_or`, …). The lemmas are
//!   stated over `Stdlib.List`s of bits, so one lemma serves every width; the
//!   per-width shape cvc5 writes is reached by computation on the concrete
//!   lists. They are always applied with those lists spelled out: unifying
//!   `map pb ?L` against a concrete list cannot be inverted (`map` is not
//!   injective), so Lambdapi could not find `L` on its own.
//!
//! - **A proof bit by bit** ([`bits_eq_steps`]) for any equation between two
//!   bit-vector terms of a concrete width built from `concat`, `extract`,
//!   `zero_extend`, the bitwise operators, literals, `@bbterm`s and
//!   uninterpreted leaves: `bv_ext_list` reduces `l = r` to the conjunction of
//!   the bit equalities, and each bit is a closed proof term chaining
//!   `alethe.bv`'s per-bit lemmas (`bit_of_concat_lo`, `bit_of_extract_in`,
//!   `bit_of_bvand`, …) down to the leaves. A proof *term* rather than a
//!   `rewrite` script: the indices it threads through (`Stdlib.Nat.5 - Stdlib.Nat.1`)
//!   only need to be convertible, never syntactically equal, to what the goal
//!   shows. When the two sides' bits agree only up to propositional logic
//!   (cvc5 writes the constant first in a slice, `⊤ ∧ p` against `p`), the bit
//!   is closed by `#cauto`.

use crate::ast::{Constant, Operator, ParamOperator, Rc, Sort, Term as AletheTerm, match_term};
use crate::translation::lambdapi::rules::rare::RareStep;
use crate::translation::lambdapi::*;
use std::ops::Deref;

/// The bits of a `@bbterm b₀ … bₙ₋₁`, least significant first, as the terms
/// `alethe.bv`'s lemmas take them in a list. `None` if `t` is not a `@bbterm`.
fn bbterm_bits(t: &Rc<AletheTerm>) -> Option<Vec<Term>> {
    match t.deref() {
        AletheTerm::Op(Operator::BvBbTerm, bits) => Some(bits.iter().map(Term::from).collect()),
        _ => None,
    }
}

/// The digits of a literal, least significant first, as `bv_literal` prints them.
fn bv_digits(v: &rug::Integer, w: usize) -> Vec<Term> {
    (0..w)
        .map(|i| Term::from(if v.get_bit(i as u32) { "true" } else { "false" }))
        .collect()
}

fn is_bbterm(t: &Rc<AletheTerm>) -> bool {
    matches!(t.deref(), AletheTerm::Op(Operator::BvBbTerm, _))
}

/// `apply ∨ᵢ₁; apply <lemma>;`: the conclusion is a unit clause whose literal
/// the lemma proves.
fn apply_lemma(lemma: Term) -> Proof {
    Proof(vec![
        ProofStep::Apply(Term::from("∨ᵢ₁"), SubProofs(None)),
        ProofStep::Apply(lemma, SubProofs(None)),
    ])
}

/// `eq_refl _`: a size side condition (`size L = n`) that holds by computation.
fn size_holds() -> Term {
    terms![Term::from("eq_refl"), Term::Underscore]
}

// ---- widths ------------------------------------------------------------------

/// The width of a bit-vector sort.
fn sort_width(s: &Sort) -> Option<usize> {
    match s {
        Sort::BitVec(w) => Some(*w),
        _ => None,
    }
}

/// The width of a (well-sorted) bit-vector term, read off its syntax: the
/// converters have no pool, and cvc5's terms carry enough to tell.
fn width(t: &Rc<AletheTerm>) -> Option<usize> {
    use AletheTerm as T;
    match t.deref() {
        T::Const(Constant::BitVec(_, w)) => Some(*w),
        T::Var(_, sort) => sort_width(sort),
        T::App(f, _) => match f.deref() {
            T::Var(_, sort) => match sort.deref() {
                Sort::Function(sorts) => sorts.last().and_then(|s| sort_width(s)),
                _ => None,
            },
            _ => None,
        },
        T::Op(Operator::BvBbTerm, bits) => Some(bits.len()),
        T::Op(Operator::BvConcat, args) => args.iter().map(width).sum(),
        T::Op(Operator::BvConst, args) => match args.as_slice() {
            [_, w] => w.as_integer()?.to_usize(),
            _ => None,
        },
        T::Op(Operator::Ite, args) => width(args.get(1)?),
        T::Op(op, args) if bv_op_name(*op).is_some() => width(args.first()?),
        T::ParamOp { op, op_args, args } => {
            let idx = |k: usize| op_args.get(k)?.as_integer()?.to_usize();
            let arg = || width(args.first()?);
            match op {
                ParamOperator::BvExtract => Some(idx(0)? - idx(1)? + 1),
                ParamOperator::ZeroExtend | ParamOperator::SignExtend => Some(idx(0)? + arg()?),
                ParamOperator::Repeat => Some(idx(0)? * arg()?),
                ParamOperator::RotateLeft | ParamOperator::RotateRight => arg(),
                _ => None,
            }
        }
        _ => None,
    }
}

/// SMT-LIB `mod`: the non-negative remainder of `a` by `b ≠ 0`.
fn rem_pos(a: &rug::Integer, b: &rug::Integer) -> rug::Integer {
    let r = rug::Integer::from(a % b);
    if r < 0 { r + rug::Integer::from(b.abs_ref()) } else { r }
}

/// The value of a closed integer term (`(+ (* 0 (int.pow2 1)) (mod 0 (int.pow2 1)))`,
/// `(- 31 (@bvsize x))`), as cvc5 writes the value of a `@bv`. `None` if it
/// mentions a variable or an operator outside `+ - * mod int.pow2 @bvsize`.
fn eval_int(t: &Rc<AletheTerm>) -> Option<rug::Integer> {
    use rug::Integer;
    match t.deref() {
        AletheTerm::Const(Constant::Integer(i)) => Some(i.clone()),
        AletheTerm::Op(op, args) => {
            let vals = || args.iter().map(eval_int).collect::<Option<Vec<_>>>();
            match op {
                Operator::Add => vals()?.into_iter().reduce(|a, b| a + b),
                Operator::Mult => vals()?.into_iter().reduce(|a, b| a * b),
                Operator::Sub => match vals()?.as_slice() {
                    [a] => Some(-a.clone()),
                    [a, rest @ ..] => Some(rest.iter().fold(a.clone(), |acc, b| acc - b)),
                    [] => None,
                },
                Operator::Mod => match vals()?.as_slice() {
                    [a, b] if *b != 0 => Some(rem_pos(a, b)),
                    _ => None,
                },
                Operator::Pow2 => match vals()?.as_slice() {
                    [k] => k.to_u32().map(|k| Integer::from(1) << k),
                    _ => None,
                },
                Operator::BvSize => args.first().and_then(width).map(Integer::from),
                _ => None,
            }
        }
        _ => None,
    }
}

// ---- the proof bit by bit ------------------------------------------------------

/// A bit-vector term, or the left-folded prefix of an n-ary one (`(concat a b c)`
/// is `concat (concat a b) c`, and its high part `concat a b` is not a term of
/// the proof).
#[derive(Clone, Copy)]
enum Node<'a> {
    Leaf(&'a Rc<AletheTerm>),
    /// `op` folded over at least two arguments.
    Fold(Operator, &'a [Rc<AletheTerm>]),
}

impl<'a> Node<'a> {
    fn of(op: Operator, args: &'a [Rc<AletheTerm>]) -> Node<'a> {
        match args {
            [t] => Node::Leaf(t),
            _ => Node::Fold(op, args),
        }
    }

    fn width(self) -> Option<usize> {
        match self {
            Node::Leaf(t) => width(t),
            Node::Fold(Operator::BvConcat, args) => args.iter().map(width).sum(),
            Node::Fold(_, args) => width(args.first()?),
        }
    }

    /// The term as the converters print it.
    fn term(self) -> Term {
        match self {
            Node::Leaf(t) => Term::from(t),
            Node::Fold(op, args) => {
                let name = Term::from(bv_op_name(op).expect("a folded bit-vector operator"));
                args.iter()
                    .map(Term::from)
                    .reduce(|acc, arg| Term::Terms(vec![name.clone(), acc, arg]))
                    .expect("a fold has arguments")
            }
        }
    }
}

/// A proof of `bit_of k t = nf`, and `nf`: the bit's normal form, with numeral
/// indices (`⊤`/`⊥` for a literal, `bit_of k x` for an uninterpreted leaf, a
/// connective of normal forms for a bitwise operator).
struct Bit {
    proof: Term,
    nf: Term,
}

fn bit_of(k: Term, t: Term) -> Term {
    terms![Term::from("bit_of"), k, t]
}

fn eqt(a: Term, b: Term) -> Term {
    terms![Term::from("eqt"), a, b]
}

fn refl(t: Term) -> Term {
    terms![Term::from("eq_refl"), t]
}

fn top() -> Term {
    Term::Alethe(LTerm::True)
}

fn bot() -> Term {
    Term::Alethe(LTerm::False)
}

/// `a - b` / `a + b` on ℕ, as the per-bit lemmas spell the index they pass on.
/// Written as sections of the qualified symbols: a proof that also opens
/// `alethe.lia` has ℤ's `+` and `-` in scope.
fn minus(a: Term, b: Term) -> Term {
    terms![operator_section("Stdlib.Nat.-"), a, b]
}

fn plus(a: Term, b: Term) -> Term {
    terms![operator_section("Stdlib.Nat.+"), a, b]
}

/// The proof of bit `k` of `node`, whose index is written `kt` in the goal
/// (`k` is its value). `None` for a shape the per-bit lemmas do not cover.
fn bit(k: usize, kt: Term, node: Node<'_>) -> Option<Bit> {
    let w = node.width()?;
    let t = node.term();
    if k >= w {
        // Beyond the width every bit is ⊥.
        return Some(Bit {
            proof: terms![Term::from("bit_of_ge"), nat(w), t, kt, intro_top()],
            nf: bot(),
        });
    }
    let leaf = |t: Term| Bit {
        proof: refl(bit_of(kt.clone(), t.clone())),
        nf: bit_of(nat(k), t),
    };
    // A literal bit computes through the rule on `bvlit`; its proof is reflexivity.
    let literal = |v: &rug::Integer| Bit {
        proof: refl(bit_of(kt.clone(), t.clone())),
        nf: if v.get_bit(k as u32) { top() } else { bot() },
    };
    // The bit of a left-folded binary operation, from its two parts.
    let binary = |op: Operator, lemma: &str, conn: Term, nf: fn(Term, Term) -> Term, a: Node<'_>, b: Node<'_>| {
        let step = terms![Term::from(lemma), nat(w), a.term(), b.term(), kt.clone()];
        let (pa, pb) = (bit(k, kt.clone(), a)?, bit(k, kt.clone(), b)?);
        let _ = op;
        Some(Bit {
            proof: eqt(step, terms![Term::from("feq2"), conn, pa.proof, pb.proof]),
            nf: nf(pa.nf, pb.nf),
        })
    };
    match node {
        Node::Fold(Operator::BvConcat, args) => {
            let (low, high) = args.split_last()?;
            let high = Node::of(Operator::BvConcat, high);
            let (wl, wh) = (width(low)?, high.width()?);
            if k < wl {
                let step = terms![
                    Term::from("bit_of_concat_lo"),
                    nat(wh),
                    nat(wl),
                    high.term(),
                    Term::from(low),
                    kt.clone(),
                    intro_top()
                ];
                let rest = bit(k, kt, Node::Leaf(low))?;
                Some(Bit { proof: eqt(step, rest.proof), nf: rest.nf })
            } else {
                let step = terms![
                    Term::from("bit_of_concat_hi"),
                    nat(wh),
                    nat(wl),
                    high.term(),
                    Term::from(low),
                    kt.clone(),
                    intro_top()
                ];
                let rest = bit(k - wl, minus(kt, nat(wl)), high)?;
                Some(Bit { proof: eqt(step, rest.proof), nf: rest.nf })
            }
        }
        Node::Fold(op @ (Operator::BvAnd | Operator::BvOr | Operator::BvXor), args) => {
            let (last, prefix) = args.split_last()?;
            let a = Node::of(op, prefix);
            match op {
                Operator::BvAnd => binary(op, "bit_of_bvand", operator_section("∧"), and_nf, a, Node::Leaf(last)),
                Operator::BvOr => binary(op, "bit_of_bvor", operator_section("∨"), or_nf, a, Node::Leaf(last)),
                _ => binary(op, "bit_of_bvxor", Term::from("xor"), xor_nf, a, Node::Leaf(last)),
            }
        }
        Node::Fold(..) => None,
        Node::Leaf(term) => match term.deref() {
            AletheTerm::Const(Constant::BitVec(v, _)) => Some(literal(v)),
            // `@bv v w`: with a closed value its bits are known; `bv_of_int w v`
            // computes to the same literal in Lambdapi.
            AletheTerm::Op(Operator::BvConst, args) => match args.first().and_then(eval_int) {
                Some(v) => Some(literal(&rem_pos(&v, &(rug::Integer::from(1) << w as u32)))),
                None => Some(leaf(t)),
            },
            AletheTerm::Op(Operator::BvBbTerm, bits) => Some(Bit {
                proof: terms![
                    Term::from("bit_of_bbterm"),
                    nat(w),
                    lp_list(bits.iter().map(Term::from).collect()),
                    kt,
                    intro_top()
                ],
                nf: Term::from(&bits[k]),
            }),
            AletheTerm::Op(op @ (Operator::BvConcat | Operator::BvAnd | Operator::BvOr | Operator::BvXor), args)
                if args.len() >= 2 =>
            {
                bit(k, kt, Node::Fold(*op, args))
            }
            AletheTerm::Op(Operator::BvNot, args) => {
                let [x] = args.as_slice() else { return None };
                // bit_of_bvnot: bit k (bvnot x) = (istrue (k < w) ∧ ¬ bit k x); k < w here.
                let step = terms![Term::from("bit_of_bvnot"), nat(w), Term::from(x), kt.clone()];
                let px = bit(k, kt, Node::Leaf(x))?;
                let cong = terms![
                    Term::from("feq2"),
                    operator_section("∧"),
                    refl(Term::Underscore),
                    terms![Term::from("feq"), operator_section("¬"), px.proof]
                ];
                Some(Bit {
                    proof: eqt(step, cong),
                    nf: and_nf(top(), Term::Alethe(LTerm::Neg(Some(Box::new(px.nf))))),
                })
            }
            AletheTerm::ParamOp { op: ParamOperator::BvExtract, op_args, args } => {
                let [x] = args.as_slice() else { return None };
                let [i, j] = <[Term; 2]>::try_from(param_op_indices(op_args)?).ok()?;
                let jv = op_args.get(1)?.as_integer()?.to_usize()?;
                // k < i - j + 1 here: the bit is bit j + k of x.
                let step = terms![
                    Term::from("bit_of_extract_in"),
                    nat(width(x)?),
                    i,
                    j.clone(),
                    Term::from(x),
                    kt.clone(),
                    intro_top()
                ];
                let rest = bit(jv + k, plus(j, kt), Node::Leaf(x))?;
                Some(Bit { proof: eqt(step, rest.proof), nf: rest.nf })
            }
            AletheTerm::ParamOp { op: ParamOperator::ZeroExtend, op_args, args } => {
                let [x] = args.as_slice() else { return None };
                let [m] = <[Term; 1]>::try_from(param_op_indices(op_args)?).ok()?;
                let step = terms![Term::from("bit_of_zero_extend"), nat(width(x)?), m, Term::from(x), kt.clone()];
                let rest = bit(k, kt, Node::Leaf(x))?;
                Some(Bit { proof: eqt(step, rest.proof), nf: rest.nf })
            }
            // Anything else -- a variable, an application, an arithmetic
            // operation -- is a leaf: its bit is its own normal form.
            _ => Some(leaf(t)),
        },
    }
}

fn and_nf(a: Term, b: Term) -> Term {
    Term::Alethe(LTerm::NAnd(vec![a, b]))
}

fn or_nf(a: Term, b: Term) -> Term {
    Term::Alethe(LTerm::NOr(vec![a, b]))
}

fn xor_nf(a: Term, b: Term) -> Term {
    terms![Term::from("xor"), a, b]
}

/// Are two bit normal forms propositionally equivalent? Decided by truth table
/// over their atoms (the bits of uninterpreted leaves, compared by their printed
/// form); `false` beyond 16 atoms. This is what `#cauto` will be asked to prove,
/// so a bit the two sides disagree on is refused here rather than at check time.
fn prop_equiv(a: &Term, b: &Term) -> bool {
    fn is_xor(v: &[Term]) -> bool {
        v.len() == 3 && matches!(&v[0], Term::TermId(s) if s == "xor")
    }
    fn atoms(t: &Term, acc: &mut Vec<String>) {
        match t {
            Term::Alethe(LTerm::True | LTerm::False) => {}
            Term::Alethe(LTerm::NAnd(ts) | LTerm::NOr(ts)) => ts.iter().for_each(|t| atoms(t, acc)),
            Term::Alethe(LTerm::Neg(Some(t))) => atoms(t, acc),
            Term::Terms(v) if is_xor(v) => v[1..].iter().for_each(|t| atoms(t, acc)),
            other => {
                let s = other.to_string();
                if !acc.contains(&s) {
                    acc.push(s);
                }
            }
        }
    }
    fn eval(t: &Term, atoms: &[String], values: u32) -> bool {
        match t {
            Term::Alethe(LTerm::True) => true,
            Term::Alethe(LTerm::False) => false,
            Term::Alethe(LTerm::NAnd(ts)) => ts.iter().all(|t| eval(t, atoms, values)),
            Term::Alethe(LTerm::NOr(ts)) => ts.iter().any(|t| eval(t, atoms, values)),
            Term::Alethe(LTerm::Neg(Some(t))) => !eval(t, atoms, values),
            Term::Terms(v) if is_xor(v) => eval(&v[1], atoms, values) ^ eval(&v[2], atoms, values),
            other => {
                let s = other.to_string();
                let i = atoms.iter().position(|a| *a == s).expect("an atom collected above");
                values & (1 << i) != 0
            }
        }
    }
    let mut ats = Vec::new();
    atoms(a, &mut ats);
    atoms(b, &mut ats);
    if ats.len() > 16 {
        return false;
    }
    (0..(1u32 << ats.len())).all(|values| eval(a, &ats, values) == eval(b, &ats, values))
}

fn prf(p: Term) -> Term {
    Term::Alethe(LTerm::ClassicProof(Box::new(p)))
}

fn eq(a: Term, b: Term) -> Term {
    Term::Alethe(LTerm::Eq(Box::new(a), Box::new(b)))
}

/// The steps proving the unit literal `l = r` bit by bit (after `apply ∨ᵢ₁`):
/// one `have hₖ : π (bit_of k l = bit_of k r)` per bit, then
/// `refine (bv_ext_list l r (∧ᵢ h_{w-1} (… (∧ᵢ h₀ ⊤ᵢ))))`, the shape
/// `bits_eq_upto w l r` computes to. `None` if a side is not a bit-vector term
/// the per-bit lemmas cover, or the widths disagree.
pub(crate) fn bits_eq_steps(l: &Rc<AletheTerm>, r: &Rc<AletheTerm>) -> Option<Vec<ProofStep>> {
    let w = width(l)?;
    if width(r)? != w {
        return None;
    }
    let (lt, rt) = (Term::from(l), Term::from(r));
    let mut steps = Vec::with_capacity(w + 1);
    let mut conj = intro_top();
    for k in 0..w {
        let (a, b) = (bit(k, nat(k), Node::Leaf(l))?, bit(k, nat(k), Node::Leaf(r))?);
        let name = format!("h{k}");
        let goal = prf(eq(bit_of(nat(k), lt.clone()), bit_of(nat(k), rt.clone())));
        let sym = |p: Term| terms![Term::from("eq_sym"), p];
        let body = if a.nf.to_string() == b.nf.to_string() {
            vec![ProofStep::Refine(eqt(a.proof, sym(b.proof)), SubProofs(None))]
        } else if !prop_equiv(&a.nf, &b.nf) {
            // The two sides really differ on this bit (or the step is beyond what
            // the per-bit lemmas see): not a proof we can offer.
            return None;
        } else {
            // The bits agree up to propositional logic: let the tautology
            // prover bridge the two normal forms.
            vec![
                ProofStep::Have(
                    "e".to_owned(),
                    prf(eq(a.nf, b.nf)),
                    vec![ProofStep::Eval(Term::from("#cauto"))],
                ),
                ProofStep::Refine(
                    eqt(a.proof, eqt(Term::from("e"), sym(b.proof))),
                    SubProofs(None),
                ),
            ]
        };
        steps.push(ProofStep::Have(name.clone(), goal, body));
        conj = terms![Term::from("∧ᵢ"), Term::from(name), conj];
    }
    steps.push(ProofStep::Refine(
        terms![Term::from("bv_ext_list"), lt, rt, conj],
        SubProofs(None),
    ));
    Some(steps)
}

/// Does a proof built by [`bits_eq_steps`] use `#cauto`?
pub(crate) fn uses_cauto(steps: &[ProofStep]) -> bool {
    steps.iter().any(|s| match s {
        ProofStep::Have(_, _, body) => uses_cauto(body),
        ProofStep::Eval(t) => t.to_string() == "#cauto",
        _ => false,
    })
}

// ---- the rules -----------------------------------------------------------------

/// Translate a bit-blasting step, `(= t t')` where `t'` is cvc5's bit-blasting
/// of `t` (`src/checker/rules/bitvectors.rs` has the shapes):
///
/// | rule | script |
/// |---|---|
/// | `bv_bitblast_step_var`: `x = @bbterm (bit_of 0 x) …` | `apply (bb_var x)` |
/// | `bv_bitblast_step_const`: `#b… = @bbterm true …` | `reflexivity` (both sides compute to the same `bvlit`) |
/// | `bv_bitblast_step_bvequal`: `(@bbterm L = @bbterm M) = (and (L₀ = M₀) …)` | `apply (bb_equal n L M ⊤ᵢ (eq_refl _) (eq_refl _))` |
/// | `bv_bitblast_step_bvadd`: `bvadd (@bbterm L) (@bbterm M) = @bbterm (ripple-carry)` | `apply (bb_add n L M (eq_refl _) (eq_refl _))` |
/// | `bv_bitblast_step_bvor/bvand/bvxor` | `apply (bb_or/bb_and/bb_xor n L M (eq_refl _) (eq_refl _))` |
/// | `bv_bitblast_step_bvnot`: `bvnot (@bbterm L) = @bbterm (not L₀ …)` | `apply (bb_not n L (eq_refl _))` |
/// | `bv_bitblast_step_extract`, `bv_bitblast_step_concat` on `@bbterm`s | `reflexivity` (the literal rules compute the sublist) |
/// | the same on other arguments, `bv_bitwise_slicing` | bit by bit ([`bits_eq_steps`]) |
///
/// `n` is the arity of the `@bbterm` and `L`, `M` its bits as lists. A rule or
/// a shape without a proof is [`TranslatorError::UnsupportedRule`], which
/// `--admit-unsupported` admits. The second component says whether the script
/// relies on `#cauto` (`alethe.tauto`).
pub fn translate_bitblast(
    rule: &str,
    clause: &[Rc<AletheTerm>],
    _premises: &[(String, &[Rc<AletheTerm>])],
) -> TradResult<(Proof, bool)> {
    let unsupported = || TranslatorError::UnsupportedRule(rule.to_owned());
    let (lhs, rhs) = clause
        .first()
        .and_then(|c| match_term!((= l r) = c))
        .ok_or_else(unsupported)?;
    let bits = |t: &Rc<AletheTerm>| bbterm_bits(t).ok_or_else(unsupported);
    let by_reflexivity = || {
        Ok((
            Proof(lambdapi! {
                apply "∨ᵢ₁";
                reflexivity;
            }),
            false,
        ))
    };
    let bit_by_bit = || {
        let steps = bits_eq_steps(lhs, rhs).ok_or_else(unsupported)?;
        let cauto = uses_cauto(&steps);
        let mut proof = vec![ProofStep::Apply(Term::from("∨ᵢ₁"), SubProofs(None))];
        proof.extend(steps);
        Ok((Proof(proof), cauto))
    };
    // The two `@bbterm`s of a binary bit-blasted operation.
    let binary = |op: Operator| -> TradResult<(Vec<Term>, Vec<Term>)> {
        match lhs.as_op() {
            Some((o, [a, b])) if o == op => Ok((bits(a)?, bits(b)?)),
            _ => Err(unsupported()),
        }
    };

    match rule {
        "bv_bitblast_step_var" => Ok((apply_lemma(terms![Term::from("bb_var"), Term::from(lhs)]), false)),
        "bv_bitblast_step_const" => by_reflexivity(),
        "bv_bitblast_step_bvequal" => {
            let (a, b) = match_term!((= a b) = lhs).ok_or_else(unsupported)?;
            let (l, m) = (bits(a)?, bits(b)?);
            Ok((
                apply_lemma(terms![
                    Term::from("bb_equal"),
                    nat(l.len()),
                    lp_list(l),
                    lp_list(m),
                    intro_top(),
                    size_holds(),
                    size_holds()
                ]),
                false,
            ))
        }
        "bv_bitblast_step_bvadd" | "bv_bitblast_step_bvor" | "bv_bitblast_step_bvand"
        | "bv_bitblast_step_bvxor" => {
            let (lemma, op) = match rule {
                "bv_bitblast_step_bvadd" => ("bb_add", Operator::BvAdd),
                "bv_bitblast_step_bvor" => ("bb_or", Operator::BvOr),
                "bv_bitblast_step_bvand" => ("bb_and", Operator::BvAnd),
                _ => ("bb_xor", Operator::BvXor),
            };
            let (l, m) = binary(op)?;
            Ok((
                apply_lemma(terms![
                    Term::from(lemma),
                    nat(l.len()),
                    lp_list(l),
                    lp_list(m),
                    size_holds(),
                    size_holds()
                ]),
                false,
            ))
        }
        "bv_bitblast_step_bvnot" => {
            let l = match lhs.as_op() {
                Some((Operator::BvNot, [a])) => bits(a)?,
                _ => return Err(unsupported()),
            };
            Ok((
                apply_lemma(terms![Term::from("bb_not"), nat(l.len()), lp_list(l), size_holds()]),
                false,
            ))
        }
        "bv_bitblast_step_extract" => match lhs.deref() {
            AletheTerm::ParamOp { op: ParamOperator::BvExtract, args, .. }
                if args.len() == 1 && is_bbterm(&args[0]) =>
            {
                by_reflexivity()
            }
            _ => bit_by_bit(),
        },
        "bv_bitblast_step_concat" => match lhs.as_op() {
            Some((Operator::BvConcat, args)) if args.iter().all(is_bbterm) => by_reflexivity(),
            _ => bit_by_bit(),
        },
        "bv_bitwise_slicing" => bit_by_bit(),
        _ => Err(unsupported()),
    }
}

/// `bvand t 0 = 0` (or `bvand 0 t = 0`): one lemma, `bvand_zero_r`/`bvand_zero_l`,
/// instead of a per-bit proof. cvc5's "failed absorb" holes have this shape, by
/// the dozen in the sqlite proofs, so the saving matters for checking time.
fn bvand_zero(lhs: &Rc<AletheTerm>, rhs: &Rc<AletheTerm>) -> Option<ProofStep> {
    let is_zero =
        |t: &Rc<AletheTerm>| matches!(t.deref(), AletheTerm::Const(Constant::BitVec(v, _)) if v.is_zero());
    if !is_zero(rhs) {
        return None;
    }
    let (a, b) = match lhs.deref() {
        AletheTerm::Op(Operator::BvAnd, args) if args.len() == 2 => (&args[0], &args[1]),
        _ => return None,
    };
    let (lemma, t) = if is_zero(b) {
        ("bvand_zero_r", a)
    } else if is_zero(a) {
        ("bvand_zero_l", b)
    } else {
        return None;
    };
    Some(ProofStep::Refine(terms![Term::from(lemma), Term::from(t)], SubProofs(None)))
}

/// `evaluate`, `aci_simp` and `ac_simp` on a bit-vector equation `(= l r)`.
///
/// - `evaluate` folds constants: `l` and `r` are closed, so `reflexivity` --
///   the literal rules compute both sides to the same digit list. A Boolean
///   result `(= (= #b… #b…) false)` is decided by `bvlit_eq_decide`.
/// - `aci_simp`/`ac_simp` reorder the arguments of `bvand`/`bvor`/`bvxor`/`concat`
///   and drop identities: proved bit by bit ([`bits_eq_steps`]), the bits that
///   only agree propositionally (`p ∧ ⊤` against `p`) by `#cauto`.
///
/// The second component says whether `#cauto` is used.
pub fn translate_bv_equation(rule: &str, clause: &[Rc<AletheTerm>]) -> TradResult<(Proof, bool)> {
    let unsupported = || TranslatorError::UnsupportedRule(rule.to_owned());
    let (lhs, rhs) = clause
        .first()
        .and_then(|c| match_term!((= l r) = c))
        .ok_or_else(unsupported)?;
    let intro = ProofStep::Apply(Term::from("∨ᵢ₁"), SubProofs(None));
    // A Boolean result: an equality between two literals, decided cellwise.
    if rhs.is_bool_true() || rhs.is_bool_false() {
        let (a, b) = match_term!((= a b) = lhs).ok_or_else(unsupported)?;
        let digits = |t: &Rc<AletheTerm>| match t.deref() {
            AletheTerm::Const(Constant::BitVec(v, w)) => Some((*w, bv_digits(v, *w))),
            _ => None,
        };
        let ((w, la), (_, lb)) = (digits(a).ok_or_else(unsupported)?, digits(b).ok_or_else(unsupported)?);
        let decide = terms![Term::from("bvlit_eq_decide"), nat(w), lp_list(la), lp_list(lb)];
        return Ok((
            Proof(vec![
                intro,
                ProofStep::Rewrite(false, None, decide, vec![], SubProofs(None)),
                ProofStep::Reflexivity,
            ]),
            false,
        ));
    }
    if width(lhs).is_none() {
        return Err(unsupported());
    }
    if let Some(step) = bvand_zero(lhs, rhs) {
        return Ok((Proof(vec![intro, step]), false));
    }
    if rule == "evaluate" {
        return Ok((Proof(vec![intro, ProofStep::Reflexivity]), false));
    }
    let steps = bits_eq_steps(lhs, rhs).ok_or_else(unsupported)?;
    let cauto = uses_cauto(&steps);
    let mut proof = vec![intro];
    proof.extend(steps);
    Ok((Proof(proof), cauto))
}

// ---- poly_simp / poly_simp_rel (alethe.bvpoly) -----------------------------------

/// cvc5's `poly_simp` over bit-vectors, `(= a b)` for two linear expressions
/// equal modulo 2ⁿ. `alethe.bvpoly` reifies both sides by rewriting (`brfy`,
/// threading one environment of atoms through both) and `bv_poly_simp` closes
/// the step once the two normal forms are convertible:
///
/// ```text
/// set r ≔ (brfy □ a); set s ≔ (brfy (r ₂) b);
/// refine (bv_poly_simp (s ₂) (r ₁) (s ₁) a b (eq_refl _) (eq_refl _) (eq_refl _));
/// ```
pub fn translate_poly_simp(clause: &[Rc<AletheTerm>]) -> TradResult<Proof> {
    let unsupported = || TranslatorError::UnsupportedRule("poly_simp".to_owned());
    let (a, b) = clause
        .first()
        .and_then(|c| match_term!((= l r) = c))
        .ok_or_else(unsupported)?;
    let (a, b) = (Term::from(a), Term::from(b));
    let proj = |x: &str, i: &str| terms![Term::from(x), Term::from(i)];
    Ok(Proof(vec![
        ProofStep::Apply(Term::from("∨ᵢ₁"), SubProofs(None)),
        ProofStep::Set("r".to_owned(), terms![Term::from("brfy"), Term::from("□"), a.clone()]),
        ProofStep::Set("s".to_owned(), terms![Term::from("brfy"), proj("r", "₂"), b.clone()]),
        ProofStep::Refine(
            terms![
                Term::from("bv_poly_simp"),
                proj("s", "₂"),
                proj("r", "₁"),
                proj("s", "₁"),
                a,
                b,
                size_holds(),
                size_holds(),
                size_holds()
            ],
            SubProofs(None),
        ),
    ]))
}

/// cvc5's `poly_simp_rel` over bit-vectors: `(= (= s t) (= u v))` from the
/// premise `(= (bvmul c₁ (bvsub s t)) (bvmul c₂ (bvsub u v)))` with odd literal
/// coefficients, i.e. units modulo 2ⁿ. The inverses d₁, d₂ are computed here and
/// passed as digit lists; `bv_poly_rel_eq` checks `dᵢ·cᵢ ≡ 1` by computation
/// (`⊤ᵢ`). Only the equality relation exists over bit-vectors.
pub fn translate_poly_simp_rel(
    clause: &[Rc<AletheTerm>],
    premise: &(String, &[Rc<AletheTerm>]),
) -> TradResult<Proof> {
    let unsupported = || TranslatorError::UnsupportedRule("poly_simp_rel".to_owned());
    let prem = premise.1.first().ok_or(TranslatorError::PremisesError)?;
    let (c1, st, c2, uv) = match prem.as_op() {
        Some((Operator::Equals, [l, r])) => match (l.as_op(), r.as_op()) {
            (Some((Operator::BvMul, [c1, st])), Some((Operator::BvMul, [c2, uv]))) => (c1, st, c2, uv),
            _ => return Err(unsupported()),
        },
        _ => return Err(unsupported()),
    };
    let sub = |t: &Rc<AletheTerm>| match t.as_op() {
        Some((Operator::BvSub, [x, y])) => Some((Term::from(x), Term::from(y))),
        _ => None,
    };
    let ((s, t), (u, v)) = (sub(st).ok_or_else(unsupported)?, sub(uv).ok_or_else(unsupported)?);
    // The coefficients and their inverses modulo 2ⁿ, as digit lists.
    let unit = |c: &Rc<AletheTerm>| -> Option<(Vec<Term>, Vec<Term>)> {
        let (value, w) = c.as_bitvector()?;
        if !value.is_odd() {
            return None;
        }
        let modulus = rug::Integer::from(1) << w as u32;
        let inverse = value.clone().invert(&modulus).ok()?;
        Some((bv_digits(&value, w), bv_digits(&inverse, w)))
    };
    let ((lc1, ld1), (lc2, ld2)) = (unit(c1).ok_or_else(unsupported)?, unit(c2).ok_or_else(unsupported)?);
    match clause.first().and_then(|c| match_term!((= l r) = c)) {
        Some((l, _)) if matches!(l.as_op(), Some((Operator::Equals, _))) => {}
        _ => return Err(unsupported()),
    }
    Ok(Proof(vec![
        ProofStep::Apply(Term::from("∨ᵢ₁"), SubProofs(None)),
        ProofStep::Refine(
            terms![
                Term::from("bv_poly_rel_eq"),
                lp_list(lc1),
                lp_list(ld1),
                lp_list(lc2),
                lp_list(ld2),
                s,
                t,
                u,
                v,
                intro_top(),
                intro_top(),
                unary_clause_to_prf(&premise.0)
            ],
            SubProofs(None),
        ),
    ]))
}

/// The structural RARE rewrites (`bv-concat-extract-merge`, `bv-extract-concat-*`,
/// `bv-extract-whole`, …): the conclusion `(= l r)` is proved bit by bit. The
/// rule's arguments are not needed: everything is read off the conclusion
/// (cvc5 passes them partially anyway).
pub fn translate_by_bits(step: &RareStep<'_>) -> Vec<ProofStep> {
    step.clause
        .first()
        .and_then(|c| match_term!((= l r) = c))
        .and_then(|(l, r)| bits_eq_steps(l, r))
        .unwrap_or_else(|| vec![ProofStep::Admit])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::translation::lambdapi::library::{Module, declared_symbols};
    use itertools::Itertools;
    use crate::translation::lambdapi::test_macros::{printed, printed_with, translate};

    const UFBV: &str = "(set-logic QF_UFBV)
         (declare-sort A 0)
         (declare-fun f ((_ BitVec 1)) A)
         (declare-fun g (A) (_ BitVec 1))
         (declare-fun x () A)
         (declare-fun y () A)
         (declare-fun a () (_ BitVec 4))
         (declare-fun b () (_ BitVec 4))
         (declare-fun c () (_ BitVec 2))
         (declare-fun d () (_ BitVec 2))";

    /// Every symbol the scripts here and in `syntax/term.rs` cite has to be
    /// declared in `alethe-lp/bv.lp`; a missing one only surfaces at
    /// `lambdapi check`.
    #[test]
    fn bv_symbols_and_lemmas_exist_in_the_library() {
        const BV_SYMBOLS: &[&str] = &[
            // the carrier, literals and bit-blast terms
            "bitvec",
            "bvlit",
            "bbterm",
            "bit_of",
            // the operators the converters print
            "bvadd",
            "bvmul",
            "bvand",
            "bvor",
            "bvxor",
            "bvnot",
            "bvneg",
            "bvsub",
            "concat",
            "extract",
            "zero_extend",
            "bvult",
            "bvule",
            "bvugt",
            "bvuge",
            "bvslt",
            "bvsle",
            "bvsgt",
            "bvsge",
            // the bit-blasting lemmas
            "bb_var",
            "bb_equal",
            "bb_add",
            "bb_or",
            "bb_and",
            "bb_xor",
            "bb_not",
            // the per-bit proofs
            "bv_ext_list",
            "eqt",
            "bit_of_ge",
            "bit_of_bbterm",
            "bit_of_concat_lo",
            "bit_of_concat_hi",
            "bit_of_extract_in",
            "bit_of_zero_extend",
            "bit_of_bvand",
            "bit_of_bvor",
            "bit_of_bvxor",
            "bit_of_bvnot",
            "bvlit_eq_decide",
        ];
        let declared = declared_symbols(Module::Bv);
        let missing = BV_SYMBOLS
            .iter()
            .filter(|s| !declared.iter().any(|d| d == *s))
            .collect_vec();
        assert!(
            missing.is_empty(),
            "alethe-lp/bv.lp does not declare {missing:?}"
        );
    }

    #[test]
    fn bitblast_var_applies_bb_var() {
        let out = printed(
            UFBV,
            "(step t1 (cl (= (g y) (@bbterm ((_ @bit_of 0) (g y))))) :rule bv_bitblast_step_var)",
        );
        assert!(out.contains("apply ∨ᵢ₁; apply (bb_var (g y));"), "{out}");
        assert!(
            out.contains("(bbterm Stdlib.Nat.1 ((bit_of Stdlib.Nat.0 (g y)) ⸬ □))"),
            "{out}"
        );
        assert!(out.contains("require open alethe.bv;"), "{out}");
    }

    #[test]
    fn bitblast_const_is_reflexivity() {
        let out = printed(
            UFBV,
            "(step t1 (cl (= #b0110 (@bbterm false true true false))) :rule bv_bitblast_step_const)",
        );
        assert!(out.contains("apply ∨ᵢ₁; reflexivity;"), "{out}");
    }

    #[test]
    fn bitblast_bvequal_applies_bb_equal() {
        let out = printed(
            UFBV,
            "(step t1 (cl (= (= (@bbterm ((_ @bit_of 0) (g x))) (@bbterm ((_ @bit_of 0) (g y))))
                              (= ((_ @bit_of 0) (g x)) ((_ @bit_of 0) (g y)))))
                 :rule bv_bitblast_step_bvequal)",
        );
        assert!(
            out.contains(
                "apply (bb_equal Stdlib.Nat.1 ((bit_of Stdlib.Nat.0 (g x)) ⸬ □) \
                 ((bit_of Stdlib.Nat.0 (g y)) ⸬ □) ⊤ᵢ (eq_refl _) (eq_refl _));"
            ),
            "{out}"
        );
    }

    /// The lists keep cvc5's order, least significant bit first.
    #[test]
    fn bitblast_bvadd_applies_bb_add_with_lsb_first_lists() {
        let out = printed(
            UFBV,
            "(step t1 (cl (= (bvadd (@bbterm ((_ @bit_of 0) c) ((_ @bit_of 1) c))
                                    (@bbterm ((_ @bit_of 0) d) ((_ @bit_of 1) d)))
                             c))
                 :rule bv_bitblast_step_bvadd)",
        );
        assert!(
            out.contains(
                "apply (bb_add Stdlib.Nat.2 ((bit_of Stdlib.Nat.0 c) ⸬ (bit_of Stdlib.Nat.1 c) ⸬ □) \
                 ((bit_of Stdlib.Nat.0 d) ⸬ (bit_of Stdlib.Nat.1 d) ⸬ □) (eq_refl _) (eq_refl _));"
            ),
            "{out}"
        );
    }

    /// `extract` and `concat` of `@bbterm`s are conversions: the literal rules
    /// compute the sublist.
    #[test]
    fn bitblast_extract_and_concat_of_bbterms_are_reflexivity() {
        let out = printed(
            UFBV,
            "(step t1 (cl (= ((_ extract 2 1) (@bbterm ((_ @bit_of 0) a) ((_ @bit_of 1) a) ((_ @bit_of 2) a) ((_ @bit_of 3) a)))
                             (@bbterm ((_ @bit_of 1) a) ((_ @bit_of 2) a))))
                 :rule bv_bitblast_step_extract)",
        );
        assert!(out.contains("apply ∨ᵢ₁; reflexivity;"), "{out}");
        let out = printed(
            UFBV,
            "(step t1 (cl (= (concat (@bbterm ((_ @bit_of 0) c) ((_ @bit_of 1) c)) (@bbterm ((_ @bit_of 0) d) ((_ @bit_of 1) d)))
                             (@bbterm ((_ @bit_of 0) d) ((_ @bit_of 1) d) ((_ @bit_of 0) c) ((_ @bit_of 1) c))))
                 :rule bv_bitblast_step_concat)",
        );
        assert!(out.contains("apply ∨ᵢ₁; reflexivity;"), "{out}");
    }

    /// `extract` of a variable is proved bit by bit: `bit_of_extract_in` on the
    /// left, `bit_of_bbterm` on the right, one `have` per bit, then
    /// `bv_ext_list`.
    #[test]
    fn bitblast_extract_of_a_variable_goes_bit_by_bit() {
        let out = printed(
            UFBV,
            "(step t1 (cl (= ((_ extract 2 1) a) (@bbterm ((_ @bit_of 1) a) ((_ @bit_of 2) a))))
                 :rule bv_bitblast_step_extract)",
        );
        assert!(out.contains("have h0 : π ((bit_of Stdlib.Nat.0 (extract Stdlib.Nat.2 Stdlib.Nat.1 a)) ="), "{out}");
        assert!(out.contains("(bit_of_extract_in Stdlib.Nat.4 Stdlib.Nat.2 Stdlib.Nat.1 a Stdlib.Nat.0 ⊤ᵢ)"), "{out}");
        assert!(out.contains("(bit_of_bbterm Stdlib.Nat.2 ((bit_of Stdlib.Nat.1 a) ⸬ (bit_of Stdlib.Nat.2 a) ⸬ □) Stdlib.Nat.0 ⊤ᵢ)"), "{out}");
        assert!(out.contains("refine (bv_ext_list (extract Stdlib.Nat.2 Stdlib.Nat.1 a) (bbterm Stdlib.Nat.2"), "{out}");
        assert!(out.contains("(∧ᵢ h1 (∧ᵢ h0 ⊤ᵢ))"), "{out}");
        assert!(!out.contains("#cauto"), "{out}");
    }

    /// cvc5 writes the constant first inside each slice: the bits agree up to
    /// commutativity, so they are closed with `#cauto` and the header opens
    /// `alethe.tauto`.
    #[test]
    fn bitwise_slicing_goes_bit_by_bit_with_cauto_for_swapped_operands() {
        let out = printed(
            UFBV,
            "(step t1 (cl (= (bvand a #b0001)
                             (concat (bvand ((_ extract 3 1) #b0001) ((_ extract 3 1) a))
                                     (bvand ((_ extract 0 0) #b0001) ((_ extract 0 0) a)))))
                 :rule bv_bitwise_slicing)",
        );
        assert!(out.contains("(bit_of_concat_hi Stdlib.Nat.3 Stdlib.Nat.1"), "{out}");
        assert!(out.contains("(bit_of_bvand Stdlib.Nat.4 a (bvlit Stdlib.Nat.4 (true ⸬ false ⸬ false ⸬ false ⸬ □)) Stdlib.Nat.0)"), "{out}");
        assert!(out.contains("eval #cauto"), "{out}");
        assert!(out.contains("require open alethe.tauto;"), "{out}");
        assert!(out.contains("refine (bv_ext_list (bvand a (bvlit"), "{out}");
    }

    /// A bit-blasting rule without a proof is unsupported, not a panic, and the
    /// flag turns it into an `admit` even though it is an `Err` out of a
    /// supported rule family.
    #[test]
    fn an_unknown_bitblast_rule_is_unsupported_and_admitted_with_the_flag() {
        let proof = "(step t1 (cl (= (bvadd a b) a)) :rule bv_bitblast_step_bvmul)";
        match translate(UFBV, proof, Config::default()) {
            Err(TranslatorError::UnsupportedRule(r)) => assert_eq!(r, "bv_bitblast_step_bvmul"),
            other => panic!("expected an unsupported rule, got {:?}", other.map(|_| ())),
        }
        let out = printed_with(
            UFBV,
            proof,
            Config {
                admit_unsupported: true,
                ..Config::default()
            },
        );
        assert!(out.contains("admit;"), "{out}");
        // A supported rule on a shape without a lemma: the same treatment.
        let proof = "(step t1 (cl (= (= a b) (and (= ((_ @bit_of 0) a) ((_ @bit_of 0) b))))) :rule bv_bitblast_step_bvequal)";
        assert!(matches!(
            translate(UFBV, proof, Config::default()),
            Err(TranslatorError::UnsupportedRule(_))
        ));
    }

    /// `poly_simp` over bit-vectors reifies both sides and normalises them in
    /// `alethe.bvpoly`, never ℤ's lemma.
    #[test]
    fn poly_simp_over_bitvectors_reflects_in_bvpoly() {
        let out = printed(UFBV, "(step t1 (cl (= (bvadd a b) (bvadd b a))) :rule poly_simp)");
        assert!(out.contains("set r ≔ (brfy □ (bvadd a b));"), "{out}");
        assert!(out.contains("set s ≔ (brfy (r ₂) (bvadd b a));"), "{out}");
        assert!(
            out.contains("refine (bv_poly_simp (s ₂) (r ₁) (s ₁) (bvadd a b) (bvadd b a) (eq_refl _) (eq_refl _) (eq_refl _))"),
            "{out}"
        );
        assert!(out.contains("require open alethe.bvpoly;"), "{out}");
        assert!(!out.contains("alethe.lia"), "{out}");
    }

    /// `poly_simp_rel`: the odd coefficients and their inverses mod 2ⁿ as digit
    /// lists (15⁻¹ = 15 and 1⁻¹ = 1 modulo 16).
    #[test]
    fn poly_simp_rel_over_bitvectors_passes_the_inverses() {
        let out = printed(
            UFBV,
            "(step t1 (cl (= (bvmul #b1111 (bvsub a b)) (bvmul #b0001 (bvsub b a)))) :rule hole)
             (step t2 (cl (= (= a b) (= b a))) :rule poly_simp_rel :premises (t1))",
        );
        assert!(
            out.contains("refine (bv_poly_rel_eq (true ⸬ true ⸬ true ⸬ true ⸬ □) (true ⸬ true ⸬ true ⸬ true ⸬ □) \
                 (true ⸬ false ⸬ false ⸬ false ⸬ □) (true ⸬ false ⸬ false ⸬ false ⸬ □) a b b a ⊤ᵢ ⊤ᵢ (π̇ₗ t1))"),
            "{out}"
        );
        // An even coefficient is not a unit: unsupported.
        let proof = "(step t1 (cl (= (bvmul #b0010 (bvsub a b)) (bvmul #b0001 (bvsub b a)))) :rule hole)
                     (step t2 (cl (= (= a b) (= b a))) :rule poly_simp_rel :premises (t1))";
        assert!(matches!(
            translate(UFBV, proof, Config::default()),
            Err(TranslatorError::UnsupportedRule(_))
        ));
    }

    #[test]
    fn evaluate_of_bitvector_literals_is_reflexivity() {
        let out = printed(UFBV, "(step t1 (cl (= ((_ extract 3 1) #b1010) #b101)) :rule evaluate)");
        assert!(out.contains("apply ∨ᵢ₁; reflexivity;"), "{out}");
        assert!(!out.contains("alethe.lia"), "{out}");
    }

    #[test]
    fn evaluate_of_a_literal_equality_is_decided_cellwise() {
        let out = printed(UFBV, "(step t1 (cl (= (= #b01 #b10) false)) :rule evaluate)");
        assert!(
            out.contains("rewrite (bvlit_eq_decide Stdlib.Nat.2 (true ⸬ false ⸬ □) (false ⸬ true ⸬ □)); reflexivity;"),
            "{out}"
        );
    }

    #[test]
    fn aci_simp_over_bitvectors_goes_bit_by_bit_with_cauto() {
        let out = printed(UFBV, "(step t1 (cl (= (bvand a b) (bvand b a))) :rule aci_simp)");
        assert!(out.contains("(bit_of_bvand Stdlib.Nat.4 a b Stdlib.Nat.0)"), "{out}");
        assert!(out.contains("eval #cauto"), "{out}");
        assert!(out.contains("require open alethe.tauto;"), "{out}");
    }

    /// `@bvsize`, `int.pow2` and `mod` print as `alethe.bvint`'s symbols, and the
    /// bridge is opened after the ℤ layer.
    #[test]
    fn bvsize_pow2_and_mod_open_the_integer_bridge() {
        let out = printed(
            UFBV,
            "(step t1 (cl (= (- 31 (@bvsize a)) 27)) :rule evaluate)
             (step t2 (cl (= (@bv (+ (* 0 (int.pow2 1)) (mod 0 (int.pow2 1))) 4) #b0000)) :rule evaluate)",
        );
        assert!(out.contains("(bvsize a)"), "{out}");
        assert!(out.contains("(Zpow2 Stdlib.Z.1)"), "{out}");
        assert!(out.contains("(Zmod Stdlib.Z.0 "), "{out}");
        assert!(out.contains("(bv_of_int Stdlib.Nat.4 ((Stdlib.Z.0 * "), "{out}");
        let lia = out.find("require open alethe.lia;").expect("lia opened");
        let bvint = out.find("require open alethe.bvint;").expect("bvint opened");
        assert!(lia < bvint, "{out}");
    }

    /// An integer comparison whose sides are closed but not numerals is still
    /// decided by computation.
    #[test]
    fn evaluate_of_a_closed_integer_comparison_is_decided_by_computation() {
        let out = printed(UFBV, "(step t1 (cl (= (>= 3 (@bvsize a)) false)) :rule evaluate)");
        assert!(out.contains("refine (Zge_false Stdlib.Z.3 (bvsize a) ⊤ᵢ)"), "{out}");
        assert!(out.contains("require open alethe.bvint;"), "{out}");
    }

    /// A `@bv` with a closed symbolic value is a literal for the per-bit proof.
    #[test]
    fn a_closed_bv_value_is_a_literal_bit_by_bit() {
        let out = printed(
            UFBV,
            "(step t1 (cl (= (bvand c (@bv (+ 1 2) 2)) (bvand (@bv 3 2) c))) :rule aci_simp)",
        );
        assert!(out.contains("eval #cauto"), "{out}");
        assert!(out.contains("(eq_refl (bit_of Stdlib.Nat.0 (bv_of_int"), "{out}");
    }

    /// cvc5's `hole`s over bit-vectors are proved when they can be: `x & 0 = 0`
    /// by one lemma, other equations by the per-bit proof; admitted otherwise.
    #[test]
    fn a_bitvector_hole_is_proved_when_it_can_be() {
        let out = printed(UFBV, "(step t1 (cl (= (bvand ((_ extract 3 1) a) #b000) #b000)) :rule hole)");
        assert!(out.contains("refine (bvand_zero_r (extract Stdlib.Nat.3 Stdlib.Nat.1 a))"), "{out}");
        assert!(!out.contains("admit"), "{out}");
        let out = printed(UFBV, "(step t1 (cl (= (bvand #b000 ((_ extract 3 1) a)) #b000)) :rule hole)");
        assert!(out.contains("refine (bvand_zero_l (extract Stdlib.Nat.3 Stdlib.Nat.1 a))"), "{out}");
        let out = printed(UFBV, "(step t1 (cl (= (bvor ((_ extract 3 1) a) #b000) ((_ extract 3 1) a))) :rule hole)");
        assert!(out.contains("refine (bv_ext_list"), "{out}");
        assert!(!out.contains("admit"), "{out}");
        let out = printed(UFBV, "(step t1 (cl (= (bvmul a b) (bvmul b a))) :rule hole)");
        assert!(out.contains("admit;"), "{out}");
    }

    /// The structural RARE rules go through the same per-bit proof.
    #[test]
    fn concat_extract_merge_goes_bit_by_bit() {
        let out = printed(
            "(set-logic QF_BV) (declare-fun x () (_ BitVec 8))",
            "(step t1 (cl (= (concat ((_ extract 0 0) x) ((_ extract 7 2) x) ((_ extract 1 1) x) ((_ extract 0 0) x))
                             (concat ((_ extract 0 0) x) ((_ extract 7 1) x) ((_ extract 0 0) x))))
                 :rule rare_rewrite :args (\"bv-concat-extract-merge\" ((_ extract 0 0) x) x ((_ extract 0 0) x)))",
        );
        assert!(out.contains("have h8 : π ("), "{out}");
        assert!(out.contains("(bit_of_concat_hi Stdlib.Nat.8 Stdlib.Nat.1 (concat (concat (extract Stdlib.Nat.0 Stdlib.Nat.0 x) (extract Stdlib.Nat.7 Stdlib.Nat.2 x)) (extract Stdlib.Nat.1 Stdlib.Nat.1 x)) (extract Stdlib.Nat.0 Stdlib.Nat.0 x) Stdlib.Nat.8 ⊤ᵢ)"), "{out}");
        assert!(out.contains("refine (bv_ext_list"), "{out}");
        assert!(!out.contains("#cauto"), "{out}");
        assert!(out.contains("require open alethe.rare.bv;"), "{out}");
    }
}
