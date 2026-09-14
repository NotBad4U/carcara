//! Scripts for the Boolean and equality RARE rewrites that are not a plain
//! `apply` of their lemma. Mirrors `alethe-lp/rare/prop.lp`.

use super::RareStep;
use crate::translation::lambdapi::*;
use crate::ast::{Operator, Rc, Term as AletheTerm};
use try_match::match_ok;

/// (define-rule bool-eq-true ((t Bool)) (= t true) t)
///
/// We translate it into:
/// ```text
/// simplify p_*;
/// rewrite ⊤=;
/// reflexivity;
/// ```
///
/// We simplify `p_*` all shared symbols otherwise the tactic `rewrite` does not work.
pub(super) fn translate_bool_eq_true(_: &RareStep<'_>) -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(false, None, "=⊤".into(), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]
}

///(define-rule bool-eq-false ((t Bool)) (= t false) (not t))
///
/// We translate it into:
/// ```text
/// simplify p_*;
/// rewrite =⊥;
/// reflexivity;
/// ```
///
/// We simplify `p_*` all shared symbols otherwise the tactic `rewrite` does not work.
pub(super) fn translate_bool_eq_false(_: &RareStep<'_>) -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(false, None, "=⊥".into(), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]
}

/// (define-rule bool-impl-false1 ((t Bool)) (=> t false) (not t))
pub(super) fn translate_bool_imp_false1(_: &RareStep<'_>) -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(false, None, "⇒⊥".into(), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]
}

/// (define-rule bool-impl-false2 ((t Bool)) (=> false t) true)
pub(super) fn translate_bool_imp_false2(_: &RareStep<'_>) -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(false, None, "⊥⇒".into(), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]
}

/// (define-rule bool-impl-true1 ((t Bool)) (=> t true) true)
pub(super) fn translate_bool_imp_true1(_: &RareStep<'_>) -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(false, None, "⇒⊤".into(), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]
}

/// (define-rule bool-impl-true2 ((t Bool)) (=> true t) t)
pub(super) fn translate_bool_imp_true2(_: &RareStep<'_>) -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(false, None, "⊤⇒".into(), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]
}

/// (define-rule bool-double-not-elim ((t Bool)) (not (not t)) t)
///
/// We translate it into:
/// ```text
/// simplify p_*;
/// rewrite ¬¬ₑ_eq;
/// reflexivity;
/// ```
///
/// We simplify `p_*` all shared symbols otherwise the tactic `rewrite` does not work.
pub(super) fn translate_bool_double_not_elim(_: &RareStep<'_>) -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(false, None, "¬¬ₑ_eq".into(), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]
}

/// Provide a proof term for the `evaluate` rule that fold boolean constant.
/// For example:
/// ```text
/// (step ti (cl (= (not true) false)) :rule rare_rewrite :args ("evaluate"))
/// ```
pub(super) fn translate_evaluate_bool() -> Vec<ProofStep> {
    // lambdapi! {
    //     simplify;
    //     apply "prop_ext";
    //     why3;
    // }
    vec![ProofStep::Admit]
}

// /// Translate (define-rule* bool-or-false ((xs Bool :list) (ys Bool :list)) (or xs false ys) (or xs ys))
pub(super) fn translate_bool_or_false(&RareStep { args, .. }: &RareStep<'_>) -> Vec<ProofStep> {
    let args = args
        .iter()
        .map(|term| unwrap_match!(**term, AletheTerm::Op(Operator::RareList, ref l) => l))
        .collect_vec();

    // If `xs` or `ys` rare-list are empty then we can not use the lemma bool-or-false because it expect 2 arguments.
    // we will use the `or_identity_l` or `or_identity_r` in that cases, otherwise we can use bool-and-true.

    if args[0].is_empty() {
        // argument `x` of and_identity_l lemma should be inferred by Lambdapi
        lambdapi! { rewrite "or_identity_l"; }
    } else if args[1].is_empty() {
        // argument `x` of and_identity_r lemma should be inferred by Lambdapi
        lambdapi! { rewrite "or_identity_r"; }
    } else {
        // let args: Vec<Term> = args
        //     .into_iter()
        //     .map(|terms| Term::from(AletheTerm::Op(Operator::RareList, terms.to_vec())))
        //     .collect_vec();
        // vec![ProofStep::Rewrite(None, Term::from("bool-or-false"), args)]
        lambdapi! { rewrite "or_identity_l"; }
    }
}

/// Translate the RARE rule:
/// `(define-rule* bool-and-true ((xs Bool :list) (ys Bool :list)) (and xs true ys) (and xs ys))`
pub(super) fn translate_bool_and_true(&RareStep { args, .. }: &RareStep<'_>) -> Vec<ProofStep> {
    let args = args
        .iter()
        .map(|term| unwrap_match!(**term, AletheTerm::Op(Operator::RareList, ref l) => l))
        .collect_vec();

    // If `xs` or `ys` rare-list are empty then we can not use the lemma bool-and-true because it expect 2 arguments.
    // we will use the `and_identity_l` or `and_identity_r` in that cases, otherwise we can use bool-and-true.

    if args[0].is_empty() {
        // argument `x` of and_identity_l lemma should be inferred by Lambdapi
        lambdapi! { rewrite "and_identity_l"; }
    } else if args[1].is_empty() {
        // argument `x` of and_identity_r lemma should be inferred by Lambdapi
        lambdapi! { rewrite "and_identity_r"; }
    } else {
        let args: Vec<Term> = args
            .into_iter()
            .map(|terms| Term::from(AletheTerm::Op(Operator::RareList, terms.clone())))
            .collect_vec();
        vec![
            ProofStep::Rewrite(
                false,
                None,
                Term::from("bool-and-true"),
                args,
                SubProofs(None),
            ),
            ProofStep::Reflexivity,
        ]
    }
}

pub(super) fn translate_bool_impl_elim(_: &RareStep<'_>) -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(
            false,
            None,
            Term::from("bool-impl-elim"),
            vec![],
            SubProofs(None),
        ),
        ProofStep::Reflexivity,
    ]
}

// // (define-rule* bool-and-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list)) (and xs (and b ys) zs) (and xs b ys zs))
pub(super) fn translate_bool_and_flatten(&RareStep { args, .. }: &RareStep<'_>) -> Vec<ProofStep> {
    let xs = 0;
    let zs = 3;

    let args_len = args
        .iter()
        .map(|term| {
            match_ok!(**term, AletheTerm::Op(Operator::RareList, ref l) => l.len())
                .or_else(|| Some(1))
                .expect("can not convert rare-list")
        })
        .collect_vec();

    if args_len[xs] == 0 {
        lambdapi! {  rewrite "∧_assoc";  }
    } else if args_len[zs] == 0 {
        vec![]
    } else {
        let args: Vec<Term> = args.iter().map(std::convert::Into::into).collect_vec();
        vec![
            ProofStep::Rewrite(
                false,
                None,
                Term::from("bool-and-flatten"),
                args,
                SubProofs(None),
            ),
            ProofStep::Reflexivity,
        ]
    }
}

/// (define-rule* bool-and-de-morgan ((x Bool) (y Bool) (zs Bool :list))
///   (not (and x y zs))
///   (not (and y zs))
///   (or (not x) _))
///
/// eval #repeat (#rewrite morgan1);
///
/// We ignore arguments for this rule and take benefits of metatactics in Lambdapi.
pub(super) fn translate_bool_and_de_morgan(_: &RareStep<'_>) -> Vec<ProofStep> {
    vec![
        ProofStep::Eval(Term::Terms(vec![
            "#repeat".into(),
            "#rewrite".into(),
            "morgan1".into(),
        ])),
        ProofStep::Reflexivity,
    ]
}

/// ```text
/// (define-rule* bool-or-de-morgan ((x Bool) (y Bool) (zs Bool :list))
///   (not (or x y zs))
///   (not (or y zs))
///   (and (not x) _))
/// ```
///
/// Translate into:
/// `eval #repeat (#rewrite morgan1);`
///
/// We ignore arguments for this rule and take benefits of metatactics in Lambdapi.
pub(super) fn translate_bool_or_de_morgan(_: &RareStep<'_>) -> Vec<ProofStep> {
    vec![
        ProofStep::Eval(Term::Terms(vec![
            "#repeat".into(),
            "#rewrite".into(),
            "morgan2".into(),
        ])),
        ProofStep::Reflexivity,
    ]
}

/// ```text
/// (define-rule* bool-or-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list))
///     (or xs (or b ys) zs)
///     (or xs b ys zs))
/// ```
///
/// Translate into:
/// `eval #repeat (#rewrite morgan1);`
///
/// We ignore arguments for this rule and take benefits of metatactics in Lambdapi.
pub(super) fn translate_bool_or_flatten(_: &RareStep<'_>) -> Vec<ProofStep> {
    vec![
        ProofStep::Eval(Term::Terms(vec![
            "#repeat".into(),
            "#rewrite".into(),
            "∨_assoc".into(),
        ])),
        ProofStep::Reflexivity,
    ]
}

/// ```text
///  (define-rule* bool-implies-or-distrib
///  ((y1 Bool) (y2 Bool) (ys Bool :list) (z Bool))
///      (=> (or y1 y2 ys) z)
///      (=> (or y2 ys) z)
///      (and (=> y1 z) _))
/// ```
pub(super) fn translate_bool_implies_or_distrib(&RareStep { args, .. }: &RareStep<'_>) -> Vec<ProofStep> {
    let mut proof = vec![];

    let y1: Term = args[0].clone().into();
    let y2: Term = args[1].clone().into();
    let ys = unwrap_match!(*args[2], AletheTerm::Op(Operator::RareList, ref l) => l);

    if ys.is_empty() {
        // argument `x` of and_identity_l lemma should be inferred by Lambdapi
        proof.push(ProofStep::Rewrite(
            false,
            None,
            "bool_implies_or_distrib".into(),
            vec![y1, y2],
            SubProofs(None),
        ));
    } else {
        let ys_term: Term = Term::from(AletheTerm::Op(Operator::RareList, ys.clone()));
        proof.push(ProofStep::Rewrite(
            false,
            None,
            "bool_implies_or_distrib_rec".into(),
            vec![y1, y2, ys_term],
            SubProofs(None),
        ));
    }

    proof.push(ProofStep::Reflexivity);

    proof
}

/// ```text
/// (define-rule* bool-or-and-distrib ((y1 Bool) (y2 Bool) (ys Bool :list) (z1 Bool) (zs Bool :list))
///   (or (and y1 y2 ys) z1 zs)
///   (or (and y2 ys) z1 zs)
///   (and (or y1 z1 zs) _))
/// ```
///
/// The fixed point distributes every conjunct of the first child. Its one-step
/// lemma, `(a ∧ b) ∨ c = (a ∨ c) ∧ (b ∨ c)`, is orthogonal and terminating as a
/// rewrite rule, so rewriting both sides of the equation to normal form makes
/// them meet, whatever else in the terms happens to match it:
/// `eval #repeat #rewrite bool-or-and-distrib; reflexivity;`
pub(super) fn translate_bool_or_and_distrib(_: &RareStep<'_>) -> Vec<ProofStep> {
    vec![
        ProofStep::Eval(Term::Terms(vec![
            "#repeat".into(),
            "#rewrite".into(),
            "bool-or-and-distrib".into(),
        ])),
        ProofStep::Reflexivity,
    ]
}

/// The number of terms a list argument stands for: a `rare-list` holds its
/// elements, and any other term is a one-element list.
fn list_len(term: &Rc<AletheTerm>) -> usize {
    match_ok!(**term, AletheTerm::Op(Operator::RareList, ref l) => l.len()).unwrap_or(1)
}

/// The name the list scripts bind their hypothesis to, unlikely to shadow a
/// symbol of the proof that the script also mentions.
const HYP: &str = "H_rare";

/// A proof `h` of the `k`-th of `n` disjuncts, lifted to their right-nested
/// disjunction: `∨ᵢ₂ (… (∨ᵢ₁ h))`, without `∨ᵢ₁` for the last disjunct.
fn inject(k: usize, n: usize, h: Term) -> Term {
    let leaf = if k + 1 == n { h } else { terms![Term::from("∨ᵢ₁"), h] };
    (0..k).fold(leaf, |t, _| terms![Term::from("∨ᵢ₂"), t])
}

/// The `k`-th of `n` conjuncts of `h`, a proof of their right-nested
/// conjunction: `∧ₑ₁ (∧ₑ₂ (… h))`, without `∧ₑ₁` for the last conjunct.
fn project(k: usize, n: usize, h: Term) -> Term {
    let spine = (0..k).fold(h, |t, _| terms![Term::from("∧ₑ₂"), t]);
    if k + 1 == n { spine } else { terms![Term::from("∧ₑ₁"), spine] }
}

/// For `(op xs w ys (not w) zs)`, the positions of `w` and `(not w)` among the
/// children of `op`, and their number. `negated_first` reads the arguments as
/// `(op xs (not w) ys w zs)` instead. The arguments are `xs w ys zs`.
fn complementary_positions(args: &[Rc<AletheTerm>], negated_first: bool) -> (usize, usize, usize) {
    let (xs, ys, zs) = (list_len(&args[0]), list_len(&args[2]), list_len(&args[3]));
    let (first, second) = (xs, xs + 1 + ys);
    let n = xs + ys + zs + 2;
    if negated_first { (second, first, n) } else { (first, second, n) }
}

/// Excluded middle on `w` proves the disjunction, each case lifted to the
/// position of its disjunct. Lambdapi wants the two cases as subproofs:
/// ```text
/// apply eq_⊤ᵢ;
/// apply ∨ₑ (em w)
/// { assume H_rare; refine ∨ᵢ₂ (… (∨ᵢ₁ H_rare)) }
/// { assume H_rare; refine ∨ᵢ₂ (… H_rare) };
/// ```
fn translate_or_taut(args: &[Rc<AletheTerm>], negated_first: bool) -> Vec<ProofStep> {
    let (w, not_w, n) = complementary_positions(args, negated_first);
    let excluded_middle = terms![Term::from("em"), Term::from(&args[1])];
    let case = |position| {
        Proof(vec![
            ProofStep::Assume(vec![HYP.to_owned()]),
            ProofStep::Refine(inject(position, n, Term::from(HYP)), SubProofs(None)),
        ])
    };
    vec![
        ProofStep::Apply(Term::from("eq_⊤ᵢ"), SubProofs(None)),
        ProofStep::Apply(
            terms![Term::from("∨ₑ"), excluded_middle],
            SubProofs(Some(vec![case(w), case(not_w)])),
        ),
    ]
}

/// `(define-rule bool-or-taut ((xs Bool :list) (w Bool) (ys Bool :list) (zs Bool :list)) (or xs w ys (not w) zs) true)`
pub(super) fn translate_bool_or_taut(&RareStep { args, .. }: &RareStep<'_>) -> Vec<ProofStep> {
    translate_or_taut(args, false)
}

/// `(define-rule bool-or-taut2 ((xs Bool :list) (w Bool) (ys Bool :list) (zs Bool :list)) (or xs (not w) ys w zs) true)`
pub(super) fn translate_bool_or_taut2(&RareStep { args, .. }: &RareStep<'_>) -> Vec<ProofStep> {
    translate_or_taut(args, true)
}

/// The conjunction refutes itself, by applying its conjunct `(not w)` to its
/// conjunct `w`:
/// ```text
/// apply eq_⊥ᵢ;
/// assume H_rare;
/// refine (∧ₑ₁ (∧ₑ₂ … H_rare)) (∧ₑ₁ (… H_rare));
/// ```
fn translate_and_conf(args: &[Rc<AletheTerm>], negated_first: bool) -> Vec<ProofStep> {
    let (w, not_w, n) = complementary_positions(args, negated_first);
    vec![
        ProofStep::Apply(Term::from("eq_⊥ᵢ"), SubProofs(None)),
        ProofStep::Assume(vec![HYP.to_owned()]),
        ProofStep::Refine(
            terms![project(not_w, n, Term::from(HYP)), project(w, n, Term::from(HYP))],
            SubProofs(None),
        ),
    ]
}

/// `(define-rule bool-and-conf ((xs Bool :list) (w Bool) (ys Bool :list) (zs Bool :list)) (and xs w ys (not w) zs) false)`
pub(super) fn translate_bool_and_conf(&RareStep { args, .. }: &RareStep<'_>) -> Vec<ProofStep> {
    translate_and_conf(args, false)
}

/// `(define-rule bool-and-conf2 ((xs Bool :list) (w Bool) (ys Bool :list) (zs Bool :list)) (and xs (not w) ys w zs) false)`
pub(super) fn translate_bool_and_conf2(&RareStep { args, .. }: &RareStep<'_>) -> Vec<ProofStep> {
    translate_and_conf(args, true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::translation::lambdapi::syntax::printer::{DEFAULT_WIDTH, PrettyPrint};

    fn print(t: Term) -> String {
        t.to_doc_with(false).pretty(DEFAULT_WIDTH).to_string()
    }

    #[test]
    fn a_disjunct_is_lifted_from_its_position() {
        let h = || Term::from("h");
        assert_eq!(print(inject(0, 3, h())), "(∨ᵢ₁ h)");
        assert_eq!(print(inject(1, 3, h())), "(∨ᵢ₂ (∨ᵢ₁ h))");
        assert_eq!(print(inject(2, 3, h())), "(∨ᵢ₂ (∨ᵢ₂ h))");
    }

    #[test]
    fn a_conjunct_is_projected_from_its_position() {
        let h = || Term::from("h");
        assert_eq!(print(project(0, 2, h())), "(∧ₑ₁ h)");
        assert_eq!(print(project(1, 3, h())), "(∧ₑ₁ (∧ₑ₂ h))");
        assert_eq!(print(project(2, 3, h())), "(∧ₑ₂ (∧ₑ₂ h))");
    }
}
