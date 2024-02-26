use std::borrow::Borrow;

use try_match::match_ok;

use crate::ast::Constant;

use super::*;

pub fn translate_rare_simp(args: &[ProofArg]) -> Proof {
    let (rare_rule, args) = args.split_first().unwrap();

    let rule: String = unwrap_match!(rare_rule, ProofArg::Term(t) => unwrap_match!(**t.borrow(), crate::ast::Term::Const(Constant::String(ref s)) => s.clone()));

    let mut rewrites = match rule.as_str() {
        "bool-and-true" => translate_bool_and_true(args),
        "bool-or-false" => translate_bool_or_false(args),
        "bool-or-flatten" => translate_bool_or_flatten(args),
        "bool-and-flatten" => translate_bool_and_flatten(args),
        "bool-impl-elim" => translate_bool_impl_elim(args),
        "evaluate" => return Proof(vec![ProofStep::Admit]), //FIXME: Need external prover setup
        r => {
            let args = args
                .into_iter()
                .map(|a| unwrap_match!(a, ProofArg::Term(t) => t).into())
                .collect_vec();
            vec![ProofStep::Rewrite(None, Term::from(r), args)]
        }
    };

    Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        inject(rewrites);
        reflexivity;
    })
}

/// Translate (define-rule* bool-or-false ((xs Bool :list) (ys Bool :list)) (or xs false ys) (or xs ys))
fn translate_bool_or_false(args: &[ProofArg]) -> Vec<ProofStep> {
    let args = args
        .into_iter()
        .map(|a| unwrap_match!(a, ProofArg::Term(t) => t))
        .map(
            |term| unwrap_match!(*(*term.borrow()), AletheTerm::Op(Operator::RareList, ref l) => l),
        )
        .collect_vec();

    // If `xs` or `ys` rare-list are empty then we can not use the lemma bool-or-false because it expect 2 arguments.
    // we will use the `or_identity_l` or `or_identity_r` in that cases, otherwise we can use bool-and-true.

    if args[0].is_empty() {
        // argument `x` of and_identity_l lemma should be inferred by Lambdapi
        lambdapi! { rewrite "or_identity_l" }
    } else if args[1].is_empty() {
        // argument `x` of and_identity_r lemma should be inferred by Lambdapi
        lambdapi! { rewrite "or_identity_r" }
    } else {
        let args: Vec<Term> = args
            .into_iter()
            .map(|terms| Term::from(AletheTerm::Op(Operator::RareList, terms.to_vec())))
            .collect_vec();
        vec![ProofStep::Rewrite(None, Term::from("bool-or-false"), args)]
    }
}

/// Translate the RARE rule:
/// `(define-rule* bool-and-true ((xs Bool :list) (ys Bool :list)) (and xs true ys) (and xs ys))`
fn translate_bool_and_true(args: &[ProofArg]) -> Vec<ProofStep> {
    let args = args
        .into_iter()
        .map(|a| unwrap_match!(a, ProofArg::Term(t) => t))
        .map(
            |term| unwrap_match!(*(*term.borrow()), AletheTerm::Op(Operator::RareList, ref l) => l),
        )
        .collect_vec();

    // If `xs` or `ys` rare-list are empty then we can not use the lemma bool-and-true because it expect 2 arguments.
    // we will use the `and_identity_l` or `and_identity_r` in that cases, otherwise we can use bool-and-true.

    if args[0].is_empty() {
        // argument `x` of and_identity_l lemma should be inferred by Lambdapi
        lambdapi! { rewrite "and_identity_l" }
    } else if args[1].is_empty() {
        // argument `x` of and_identity_r lemma should be inferred by Lambdapi
        lambdapi! { rewrite "and_identity_r" }
    } else {
        let args: Vec<Term> = args
            .into_iter()
            .map(|terms| Term::from(AletheTerm::Op(Operator::RareList, terms.to_vec())))
            .collect_vec();
        vec![ProofStep::Rewrite(None, Term::from("bool-and-true"), args)]
    }
}

fn translate_bool_impl_elim(args: &[ProofArg]) -> Vec<ProofStep> {
    let args = args
        .into_iter()
        .map(|a| unwrap_match!(a, ProofArg::Term(t) => t).into())
        .collect_vec();
    vec![ProofStep::Rewrite(None, Term::from("bool-impl-elim"), args)]
}

/// Translate the RARE rule:
/// `(define-rule* bool-or-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list)) (or xs (or b ys) zs) (or xs b ys zs))`
fn translate_bool_or_flatten(args: &[ProofArg]) -> Vec<ProofStep> {
    let xs = 0;
    let zs = 3;

    let args_len = args
        .iter()
        .map(|a| unwrap_match!(a, ProofArg::Term(t) => t))
        .map(|term| {
            match_ok!(*(*term.borrow()), AletheTerm::Op(Operator::RareList, ref l) => l.len())
                .or_else(|| Some(1))
                .expect("can not convert rare-list")
        })
        .collect_vec();

    if args_len[xs] == 0 {
        lambdapi! {  rewrite "left ∨ᶜ_assoc_eq"  }
    } else if args_len[zs] == 0 {
        vec![]
    } else {
        let args: Vec<Term> = args
            .into_iter()
            .map(|a| unwrap_match!(a, ProofArg::Term(t) => t).into())
            .collect_vec();
        vec![ProofStep::Rewrite(
            None,
            Term::from("bool-or-flatten"),
            args,
        )]
    }
}

// (define-rule* bool-and-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list)) (and xs (and b ys) zs) (and xs b ys zs))
fn translate_bool_and_flatten(args: &[ProofArg]) -> Vec<ProofStep> {
    let xs = 0;
    let zs = 3;

    let args_len = args
        .iter()
        .map(|a| unwrap_match!(a, ProofArg::Term(t) => t))
        .map(|term| {
            match_ok!(*(*term.borrow()), AletheTerm::Op(Operator::RareList, ref l) => l.len())
                .or_else(|| Some(1))
                .expect("can not convert rare-list")
        })
        .collect_vec();

    if args_len[xs] == 0 {
        lambdapi! {  rewrite "left ∧ᶜ_assoc_eq"  }
    } else if args_len[zs] == 0 {
        vec![]
    } else {
        let args: Vec<Term> = args
            .into_iter()
            .map(|a| unwrap_match!(a, ProofArg::Term(t) => t).into())
            .collect_vec();
        vec![ProofStep::Rewrite(
            None,
            Term::from("bool-and-flatten"),
            args,
        )]
    }
}

pub fn translate_simplify_step(rule: &str) -> Proof {
    match rule {
        "equiv_simplify" => translate_equiv_simplify(),
        "not_simplify" => translate_not_simplify(),
        "implies_simplify" => translate_implies_simplify(),
        "ite_simplify" => translate_ite_simplify(),
        "ac_simp" => translate_ac_simplify(),
        "all_simplify" => Proof(vec![ProofStep::Admit]),
        r => unimplemented!("{}", r),
    }
}

fn translate_equiv_simplify() -> Proof {
    Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        try [ rewrite ."[ x in x = _ ]" "equiv_simplify₁" ];
        try [ rewrite ."[ x in x = _ ]" "equiv_simplify₂"  ];
        try [ rewrite ."[ x in x = _ ]" "equiv_simplify₃"  ];
        try [ rewrite ."[ x in x = _ ]" "equiv_simplify₄"  ];
        try [ rewrite ."[ x in x = _ ]" "equiv_simplify₅"  ];
        try [ rewrite ."[ x in x = _ ]" "equiv_simplify₆"  ];
        try [ rewrite ."[ x in x = _ ]" "equiv_simplify₇"  ];
        try [ rewrite ."[ x in x = _ ]" "equiv_simplify₈"  ];
        reflexivity;
    })
}

fn translate_not_simplify() -> Proof {
    Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        try [ rewrite ."[ x in x = _ ]" "not_simplify₁" ];
        try [ rewrite ."[ x in x = _ ]" "not_simplify₂"  ];
        try [ rewrite ."[ x in x = _ ]" "not_simplify₃"  ];
        reflexivity;
    })
}

fn translate_implies_simplify() -> Proof {
    Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        try [ rewrite "implies_simplify₁" ];
        try [ rewrite "implies_simplify₂"  ];
        try [ rewrite "implies_simplify₃"  ];
        try [ rewrite "implies_simplify₄"  ];
        try [ rewrite "implies_simplify₅"  ];
        try [ rewrite "implies_simplify₆"  ];
        try [ rewrite "implies_simplify₇"  ];
        try [ rewrite "implies_simplify₈"  ];
        reflexivity;
    })
}

fn translate_ite_simplify() -> Proof {
    Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        try [ rewrite "ite_simplify₁" ];
        try [ rewrite "ite_simplify₂"  ];
        try [ rewrite "ite_simplify₃"  ];
        try [ rewrite "ite_simplify₄"  ];
        try [ rewrite "ite_simplify₅"  ];
        try [ rewrite "ite_simplify₆"  ];
        try [ rewrite "ite_simplify₇"  ];
        try [ rewrite "ite_simplify₈"  ];
        try [ rewrite "ite_simplify₉"  ];
        try [ rewrite "ite_simplify₁₀"  ];
        try [ rewrite "ite_simplify₁₁"  ];
        try [ rewrite "ite_simplify₁₂"  ];
        reflexivity;
    })
}

fn translate_ac_simplify() -> Proof {
    Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        try [ rewrite "ac_simp_or" ];
        try [ rewrite "ac_simp_and"  ];
        reflexivity;
    })
}
