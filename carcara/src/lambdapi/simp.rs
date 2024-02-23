use std::borrow::Borrow;

use crate::ast::Constant;

use super::*;

pub fn translate_rare_simp(args: &[ProofArg]) -> Proof {
    let (rare_rule, args) = args.split_first().unwrap();

    let rule: String = unwrap_match!(rare_rule, ProofArg::Term(t) => unwrap_match!(**t.borrow(), crate::ast::Term::Const(Constant::String(ref s)) => s.clone()));

    let mut rewrites = match rule.as_str() {
        "bool-and-true" => return Proof(vec![ProofStep::Admit]),
        "bool-or-flatten" => return Proof(vec![ProofStep::Admit]), //translate_bool_or_flatten(args).0,
        "bool-and-flatten" => return Proof(vec![ProofStep::Admit]), //translate_bool_and_flatten(args).0,
        "bool-impl-elim" => translate_bool_impl_elim(args).0,
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

fn translate_bool_impl_elim(args: &[ProofArg]) -> Proof {
    let args = args
        .into_iter()
        .map(|a| unwrap_match!(a, ProofArg::Term(t) => t).into())
        .collect_vec();
    Proof(vec![
        ProofStep::Rewrite(
            Some("[in x in _ = x]".to_string()),
            Term::TermId("or_identity".to_string()),
            vec![],
        ),
        ProofStep::Rewrite(None, Term::from("bool-impl-elim"), args),
    ])
}

// (define-rule* bool-or-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list)) (or xs (or b ys) zs) (or xs b ys zs))
fn translate_bool_or_flatten(args: &[ProofArg]) -> Proof {
    let args_terms: Vec<Term> = args
        .into_iter()
        .map(|a| unwrap_match!(a, ProofArg::Term(t) => t).into())
        .collect_vec();
    Proof(vec![ProofStep::Admit])
    
    //println!("{:#?}", args_terms);

    // let args =  args_terms
    //     .into_iter()
    //     .map(|t| unwrap_match!(t, Term::Terms(v) => Term::Alethe(LTerm::NOr(v))))
    //     .collect_vec();

    //println!("{:?}", args);

    // if matches!(args.last(), Some(Term::Alethe(LTerm::NOr(_)))) == false {
    //     if let Some(zs) = args.last_mut() {
    //         *zs = Term::Alethe(LTerm::NOr(vec![zs.clone(), Term::Alethe(LTerm::False)]));
    //     }
    // }

    // // Remove the trailing `⊥` in `ys` sublist by `or_identity ys`
    // let ys_index: usize = 2;
    // let mut rewrites: Vec<ProofStep> = vec![ProofStep::Rewrite(
    //     None,
    //     Term::from("or_identity"),
    //     vec![args[ys_index].clone()],
    // )];

    // if matches!(&args[0], Term::TermId(s) if s == "") {
    //     rewrites.push(ProofStep::Rewrite(
    //         None,
    //         Term::from("bool-or-flatten'"),
    //         args,
    //     ))
    // } else {
    //     rewrites.push(ProofStep::Rewrite(
    //         None,
    //         Term::from("bool-or-flatten"),
    //         args,
    //     ))
    // }

    // Proof(rewrites)
    //todo!()
}

// (define-rule* bool-and-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list)) (and xs (and b ys) zs) (and xs b ys zs))
fn translate_bool_and_flatten(args: &[ProofArg]) -> Proof {
    // let mut args: Vec<Term> = args
    //     .into_iter()
    //     .map(|a| unwrap_match!(a, ProofArg::Term(t) => t).into())
    //     .collect_vec();

    // if let Some(zs) = args.last_mut() {
    //     *zs = Term::Alethe(LTerm::NAnd(vec![zs.clone(), Term::Alethe(LTerm::True)]));
    // }

    // // Remove the trailing `⊤`` in `ys` sublist by `and_identity ys`
    // let ys_index: usize = 2;
    // let mut rewrites: Vec<ProofStep> = vec![ProofStep::Rewrite(
    //     None,
    //     Term::from("and_identity"),
    //     vec![args[ys_index].clone()],
    // )];

    // if matches!(&args[0], Term::TermId(s) if s == "") {
    //     rewrites.push(ProofStep::Rewrite(
    //         None,
    //         Term::from("bool-and-flatten'"),
    //         args,
    //     ))
    // } else {
    //     rewrites.push(ProofStep::Rewrite(
    //         None,
    //         Term::from("bool-and-flatten"),
    //         args,
    //     ))
    // }

    // Proof(rewrites)
    Proof(vec![ProofStep::Admit])
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

// FIXME: check from the clause between or_identity or and_identity need to be apply
fn translate_ac_simplify() -> Proof {
    Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        try [ rewrite "or_identity" ]; //FIXME: Can not rewrite if (or a (or a bot)) = (or a bot)
        try [ rewrite "and_identity" ];
        try [ rewrite "ac_simp_or" ];
        try [ rewrite "ac_simp_and"  ];
        reflexivity;
    })
}
