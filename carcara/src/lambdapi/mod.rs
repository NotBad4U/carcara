use crate::ast::{
    deep_eq, Identifier, Operator, ProblemPrelude, Proof as ProofElaborated, ProofArg,
    ProofCommand, ProofIter, ProofStep as AstProofStep, Rc, Sort, Term as AletheTerm, Terminal,
};
use itertools::intersperse;
use std::fmt::{self, write};
use std::time::Duration;

#[inline]
fn TYPE() -> Term {
    Term::TermId("TYPE".into())
}

#[inline]
fn bottom() -> Term {
    Term::TermId("⊥".into())
}

#[derive(Debug, Clone, PartialEq)]
enum BuiltinSort {
    Bool,
}

impl fmt::Display for BuiltinSort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BuiltinSort::Bool => write!(f, "Prop"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Modifier {
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

#[derive(Debug, Clone)]
enum Command {
    RequireOpen(String),
    Symbol(Option<Modifier>, String, Vec<Param>, Term, Option<Proof>),
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Command::RequireOpen(path) => write!(f, "open require {};", path),
            Command::Symbol(modifier, name, params, term, None) => {
                let params = params
                    .iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<_>>()
                    .join(" ");
                writeln!(
                    f,
                    "{}symbol {} {}: {};",
                    modifier
                        .as_ref()
                        .map(|m| format!("{} ", m))
                        .unwrap_or(String::new()),
                    name,
                    params,
                    term
                )
            }
            Command::Symbol(modifier, name, params, term, Some(term_proof)) => {
                let params = params
                    .iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<_>>()
                    .join(" ");
                writeln!(
                    f,
                    "{}symbol {} {}: {} ≔",
                    modifier
                        .as_ref()
                        .map(|m| format!("{} ", m))
                        .unwrap_or(String::new()),
                    name,
                    params,
                    term
                )?;
                writeln!(f, "begin")?;
                write!(f, "{}", term_proof)?;
                writeln!(f, "end;")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Term {
    Sort(BuiltinSort),
    TermId(String),
    Terms(Vec<Term>),
    Applications(Vec<Term>),
}

struct Clauses(Vec<Term>);

impl fmt::Display for Clauses {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ts: String = intersperse(self.0.clone(), Term::TermId("⟇".to_string()))
            .map(|e| format!("{}", e))
            .collect::<Vec<_>>()
            .join(" ");
        write!(f, "{}", ts)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::Sort(bs) => write!(f, "{}", bs),
            Term::TermId(id) => write!(f, "{}", id),
            Term::Applications(terms) => write!(
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
                        .join(" ")
                )
            }
            _ => unimplemented!(),
        }
    }
}

impl From<AletheTerm> for Term {
    fn from(term: AletheTerm) -> Self {
        match term {
            AletheTerm::Sort(sort) => match sort {
                Sort::Function(params) => Term::Applications(
                    params
                        .into_iter()
                        .map(|p| Term::from(Rc::unwrap_or_clone(p)))
                        .collect(),
                ),
                Sort::Atom(id, terms) => Term::TermId(id),
                Sort::Bool => Term::Sort(BuiltinSort::Bool),
                s => todo!("{:#?}", s),
            },
            AletheTerm::App(f, args) => {
                let mut func = vec![Term::from(Rc::unwrap_or_clone(f))];
                let mut args: Vec<Term> = args
                    .into_iter()
                    .map(|a| Term::from(Rc::unwrap_or_clone(a)))
                    .collect();
                func.append(&mut args);
                Term::Terms(func)
            }
            AletheTerm::Op(operator, args) => match operator {
                Operator::Not => {
                    let mut not = vec![Term::TermId("¬".to_string())];
                    let mut args: Vec<Term> = args
                        .into_iter()
                        .map(|a| Term::from(Rc::unwrap_or_clone(a)))
                        .collect();
                    not.append(&mut args);
                    Term::Terms(not)
                }
                Operator::Or => {
                    let mut terms = args
                        .into_iter()
                        .map(|a| {
                            vec![
                                Term::from(Rc::unwrap_or_clone(a)),
                                Term::TermId("∨".to_string()),
                            ]
                        })
                        .flatten()
                        .collect::<Vec<_>>();
                    terms.pop(); //remove trailling disjunction
                    Term::Terms(terms)
                }
                Operator::Equals => {
                    let left = Term::from(Rc::unwrap_or_clone(args[0].clone()));
                    let right = Term::from(Rc::unwrap_or_clone(args[1].clone()));

                    Term::Terms(vec![left, Term::TermId("=".to_string()), right])
                }
                o => todo!("missing operator {}", o),
            },
            AletheTerm::Lambda(..) => todo!("lambda"),
            AletheTerm::Let(..) => todo!("let"),
            AletheTerm::Terminal(terminal) => match terminal {
                Terminal::String(id) => Term::TermId(id),
                Terminal::Var(Identifier::Simple(id), ..) => Term::TermId(id),
                t => todo!("{:#?}", t),
            },
            e => todo!("{:#?}", e),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct BinderAnonymous {
    param: Vec<String>,
    term: Term,
}

#[derive(Debug, Clone, PartialEq)]
struct Binder {
    param: (String, Term),
    term: Term,
}

#[derive(Debug, Clone, PartialEq)]
struct Param(String, Term);

impl fmt::Display for Param {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Param(id, _term) => write!(f, "{}", id),
        }
    }
}

#[derive(Debug, Clone)]
struct Proof(Vec<ProofStep>);

impl fmt::Display for Proof {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Proof(steps) => {
                steps.iter().for_each(|s| writeln!(f, "{}", s).unwrap());
                Ok(())
            }
        }
    }
}

#[derive(Debug, Clone)]
enum ProofStep {
    Apply(Term, Vec<Term>),
    Have(String, Term, Vec<ProofStep>),
    Admit,
    Reflexivity,
}

impl fmt::Display for ProofStep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ProofStep::Have(id, term, proof) => {
                let proof_steps_fmt: String = proof.iter().map(|p| format!("{}", p)).collect();
                let have_fmt = format!("have {} : π {} {{ {} }};\n", id, term, proof_steps_fmt);
                write!(f, "{}", have_fmt)
            }
            ProofStep::Apply(t, args) => {
                write!(
                    f,
                    "apply @{} {};",
                    t,
                    args.iter()
                        .map(|i| format!("{}", i))
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
            ProofStep::Admit => write!(f, "admit;"),
            ProofStep::Reflexivity => write!(f, "simplify; reflexivity;"),
        }
    }
}

/// Translate the SMT declaration symbol of sort and function into Lambdapi symbol.
/// The type Prop is used a default to be polymorphic.
/// ex:
/// (declare-sort S 0)
/// become
/// symbol S: Prop;
fn export_prelude(prelude: ProblemPrelude) -> Vec<Command> {
    let mut sort_declarations_symbols = prelude
        .sort_declarations
        .iter()
        .map(|(id, _)| {
            Command::Symbol(
                Some(Modifier::Constant),
                id.to_string(),
                vec![],
                TYPE(),
                None,
            )
        })
        .collect::<Vec<Command>>();

    let mut function_declarations_symbols = prelude
        .function_declarations
        .into_iter()
        .map(|(id, term)| {
            Command::Symbol(
                None,
                id.to_string(),
                vec![],
                Term::from(Rc::unwrap_or_clone(term)),
                None,
            )
        })
        .collect::<Vec<Command>>();

    sort_declarations_symbols.append(&mut function_declarations_symbols);

    sort_declarations_symbols
}

fn header_modules() -> Vec<Command> {
    vec![
        Command::RequireOpen("Stdlib.Set".into()),
        Command::RequireOpen("Stdlib.Prop".into()),
        Command::RequireOpen("Stdlib.FOL".into()),
        Command::RequireOpen("Stdlib.FOL".into()),
    ]
}

fn arg_is_false(ts: Vec<Term>) -> Vec<Term> {
    if ts.is_empty() {
        vec![bottom()]
    } else {
        ts
    }
}

fn export_proof_step(proof_elaborated: ProofElaborated) -> Proof {
    let proof_iter: ProofIter = proof_elaborated.iter();
    let mut steps = vec![];

    for command in proof_elaborated.commands.iter() {
        let step = match command {
            ProofCommand::Assume { id, term } => ProofStep::Have(
                id.to_string(),
                Term::from(Rc::unwrap_or_clone(term.clone())),
                vec![ProofStep::Admit],
            ),
            ProofCommand::Step(AstProofStep {
                id,
                clause,
                premises,
                rule,
                args,
                discharge: _,
            }) if rule == "resolution" || rule == "th_resolution" => {
                let ps: Vec<Vec<_>> = premises
                    .clone()
                    .into_iter()
                    .map(|p| match proof_iter.get_premise(p) {
                        ProofCommand::Assume { id: _, term } => {
                            vec![term.clone()]
                        }
                        ProofCommand::Step(AstProofStep { id: _, clause, .. }) => clause.to_vec(),
                        _ => unreachable!(),
                    })
                    .collect();

                let premises_id: Vec<_> = premises
                    .into_iter()
                    .map(|p| match proof_iter.get_premise(*p) {
                        ProofCommand::Assume { id, .. } => id,
                        ProofCommand::Step(AstProofStep { id, .. }) => id,
                        _ => unreachable!(),
                    })
                    .collect();

                // Construct each resolution step
                // 1- construct the base case
                let (left, right) = ps.split_at(2);
                let (arg, args) = args.split_at(2);

                let (pivot, flag): (&Rc<AletheTerm>, &Rc<AletheTerm>) = match arg {
                    [ProofArg::Term(pivot), ProofArg::Term(flag)] => (pivot, flag),
                    _ => unreachable!("We expect only args in a format [ Pivot, Bool, ...]"),
                };

                let (mut a, mut b) =
                    if let AletheTerm::Terminal(Terminal::Var(Identifier::Simple(s), _)) =
                        (**flag).clone()
                    {
                        if s == "true" {
                            let a: Vec<Rc<_>> = left[1]
                                .clone()
                                .into_iter()
                                .filter(|x| !deep_eq(x, pivot, &mut Duration::ZERO))
                                .collect();
                            let b: Vec<Rc<_>> = left[0]
                                .clone()
                                .into_iter()
                                .filter(|x| {
                                    !deep_eq(
                                        x,
                                        &Rc::from(AletheTerm::Op(
                                            Operator::Not,
                                            vec![Rc::from(pivot.clone())],
                                        )),
                                        &mut Duration::ZERO,
                                    )
                                })
                                .collect();
                            (a, b)
                        } else {
                            let a: Vec<Rc<_>> = left[0]
                                .clone()
                                .into_iter()
                                .filter(|x| {
                                    !deep_eq(
                                        x,
                                        &Rc::from(AletheTerm::Op(
                                            Operator::Not,
                                            vec![Rc::from(pivot.clone())],
                                        )),
                                        &mut Duration::ZERO,
                                    )
                                })
                                .collect();
                            let b: Vec<Rc<_>> = left[1]
                                .clone()
                                .into_iter()
                                .filter(|x| !deep_eq(x, pivot, &mut Duration::ZERO))
                                .collect();
                            (a, b)
                        }
                    } else {
                        unreachable!()
                    };

                let mut a_print: Vec<Term> = a
                    .clone()
                    .into_iter()
                    .map(|a| {
                        vec![
                            Term::from(Rc::unwrap_or_clone(a.clone())),
                            Term::TermId("⟇".to_string()),
                        ]
                    })
                    .flatten()
                    .collect::<Vec<_>>();

                a_print.pop(); //remove trailling ⟇

                let mut b_print: Vec<Term> = b
                    .clone()
                    .into_iter()
                    .map(|a| {
                        vec![
                            Term::from(Rc::unwrap_or_clone(a.clone())),
                            Term::TermId("⟇".to_string()),
                        ]
                    })
                    .flatten()
                    .collect::<Vec<_>>();

                b_print.pop(); //remove trailling ⟇

                let goal_print: Vec<Term> = if a.is_empty() == false && b.is_empty() == false {
                    arg_is_false(
                        vec![a_print, vec![Term::TermId("⟇".into())], b_print]
                            .into_iter()
                            .flatten()
                            .collect(),
                    )
                } else {
                    if b.is_empty() {
                        arg_is_false(a_print)
                    } else {
                        arg_is_false(b_print)
                    }
                };

                let a_print: Vec<Term> = a
                    .clone()
                    .into_iter()
                    .map(|term| Term::from(Rc::unwrap_or_clone(term.clone())))
                    .intersperse(Term::TermId("⟇".to_string()))
                    .collect();


                a.append(&mut b);


                let arguments = vec![
                    Term::from(Rc::unwrap_or_clone(pivot.clone())),
                    Term::Terms(arg_is_false(a_print)),
                    Term::Terms(arg_is_false(
                        b.into_iter()
                            .map(|term| Term::from(Rc::unwrap_or_clone(term.clone())))
                            .collect(),
                    )),
                    Term::TermId(premises_id[0].to_string()),
                    Term::TermId(premises_id[1].to_string()),
                ];

                let base = ProofStep::Have(
                    format!("{}_1", id),
                    Term::Terms(goal_print),
                    vec![ProofStep::Apply(
                        Term::TermId("resolutionᵣ".into()),
                        arguments,
                    )], //TODO: consider also resolutionl
                );

                let chunck_args = args.chunks(2);

                let mut resolution_steps = (*right)
                    .into_iter()
                    .zip(premises_id.iter().skip(2))
                    .zip(chunck_args)
                    .fold(vec![base], |mut acc, ((premise, cur_premise_id), args)| {
                        let last_step: &ProofStep = acc.last().unwrap();

                        let last_goal_term = match last_step.clone() {
                            ProofStep::Have(_id, Term::Terms(goal), ..) => goal
                                .into_iter()
                                .filter(|t| !matches!(t, Term::TermId(s) if *s == "⟇".to_string()))
                                .collect(),
                            ProofStep::Have(_id, goal, ..) => vec![goal],
                            _ => unreachable!(),
                        };

                        let (pivot, flag): (&Rc<AletheTerm>, &Rc<AletheTerm>) = match args {
                            [ProofArg::Term(pivot), ProofArg::Term(flag)] => (pivot, flag),
                            _ => {
                                unreachable!("We expect only args in a format [ Pivot, Bool, ...]")
                            }
                        };

                        let (mut a, b) =
                            if let AletheTerm::Terminal(Terminal::Var(Identifier::Simple(s), _)) =
                                (**flag).clone()
                            {
                                if s == "true" {
                                    let a: Vec<Term> = last_goal_term
                                        .clone()
                                        .into_iter()
                                        .filter(|x| *x != Term::from((**pivot).clone()))
                                        .collect();

                                    let b: Vec<Rc<_>> = premise
                                        .clone()
                                        .into_iter()
                                        .filter(|x| {
                                            !deep_eq(
                                                x,
                                                &Rc::from(AletheTerm::Op(
                                                    Operator::Not,
                                                    vec![Rc::from(pivot.clone())],
                                                )),
                                                &mut Duration::ZERO,
                                            )
                                        })
                                        .collect();
                                    (a, b)
                                } else {
                                    let a: Vec<Term> = last_goal_term
                                        .clone()
                                        .into_iter()
                                        .filter(|x| {
                                            *x != Term::Terms(vec![
                                                Term::TermId("¬".to_string()),
                                                Term::from((**pivot).clone()),
                                            ])
                                        })
                                        .collect();
                                    let b: Vec<Rc<_>> = premise
                                        .clone()
                                        .into_iter()
                                        .filter(|x| !deep_eq(x, pivot, &mut Duration::ZERO))
                                        .collect();
                                    (a, b)
                                }
                            } else {
                                unreachable!()
                            };

                        let mut b: Vec<Term> = b
                            .into_iter()
                            .map(|a| {
                                vec![
                                    Term::from(Rc::unwrap_or_clone(a.clone())),
                                    Term::TermId("⟇".to_string()),
                                ]
                            })
                            .flatten()
                            .collect::<Vec<_>>();

                        b.pop(); //remove trailling ⟇

                        let arguments = vec![
                            Term::from(Rc::unwrap_or_clone(pivot.clone())),
                            Term::Terms(arg_is_false(a.clone())),
                            Term::Terms(arg_is_false(b.clone())),
                            Term::TermId(format!("{}_{}", id, acc.len())),
                            Term::TermId(cur_premise_id.to_string()),
                        ];

                        let mut goal = a;
                        goal.append(&mut b);

                        let new_step = ProofStep::Have(
                            format!("{}_{}", id, acc.len() + 1),
                            Term::Terms(arg_is_false(goal)),
                            vec![ProofStep::Apply(
                                Term::TermId("resolutionᵣ".into()),
                                arguments,
                            )],
                        );

                        acc.push(new_step);
                        acc
                    });

                resolution_steps.push(ProofStep::Apply(
                    Term::TermId(format!("{}_{}", id, resolution_steps.len())),
                    vec![],
                ));

                let mut terms_clause = clause
                    .into_iter()
                    .map(|a| {
                        vec![
                            Term::from(Rc::unwrap_or_clone(a.clone())),
                            Term::TermId("⟇".to_string()),
                        ]
                    })
                    .flatten()
                    .collect::<Vec<_>>();
                terms_clause.pop(); //remove trailling ⟇

                let clause = if terms_clause.is_empty() {
                    bottom()
                } else {
                    Term::Terms(terms_clause)
                };

                ProofStep::Have(id.to_string(), clause, resolution_steps)
            }
            ProofCommand::Step(AstProofStep {
                id,
                clause,
                premises,
                rule,
                args,
                discharge,
            }) if rule.contains("simp") => {
                let mut terms_clause = clause
                    .into_iter()
                    .map(|a| {
                        vec![
                            Term::from(Rc::unwrap_or_clone(a.clone())),
                            Term::TermId("⟇".to_string()),
                        ]
                    })
                    .flatten()
                    .collect::<Vec<_>>();
                terms_clause.pop(); //remove trailling ⟇

                ProofStep::Have(
                    id.to_string(),
                    Term::Terms(terms_clause),
                    vec![ProofStep::Reflexivity],
                )
            }
            ProofCommand::Step(AstProofStep { id, clause, premises, rule, .. })
                if rule.contains("or") =>
            {
                let premise = premises
                    .first()
                    .map(|p| match proof_iter.get_premise(*p) {
                        ProofCommand::Assume { id, .. } => Term::TermId(id.clone()),
                        ProofCommand::Step(AstProofStep { id, .. }) => Term::TermId(id.clone()),
                        _ => unreachable!(),
                    })
                    .unwrap();

                // Convert clauses
                let mut terms_clause = clause
                    .into_iter()
                    .map(|a| {
                        vec![
                            Term::from(Rc::unwrap_or_clone(a.clone())),
                            Term::TermId("⟇".to_string()),
                        ]
                    })
                    .flatten()
                    .collect::<Vec<_>>();
                terms_clause.pop(); //remove trailling ⟇

                ProofStep::Have(
                    id.to_string(),
                    Term::Terms(terms_clause),
                    vec![ProofStep::Apply(premise, vec![])],
                )
            }
            ProofCommand::Step(AstProofStep { id, clause, premises, rule, .. }) => {
                // Prepare premises
                let mut ps: Vec<Term> = Vec::new();
                if premises.len() > 0 {
                    ps = premises
                        .iter()
                        .map(|p| match proof_iter.get_premise(*p) {
                            ProofCommand::Assume { id, .. } => Term::TermId(id.clone()),
                            ProofCommand::Step(AstProofStep { id, .. }) => Term::TermId(id.clone()),
                            _ => unreachable!(),
                        })
                        .collect();
                }

                let args = get_args(&rule, clause);

                // Convert clauses
                let mut terms_clause = clause
                    .into_iter()
                    .map(|a| {
                        vec![
                            Term::from(Rc::unwrap_or_clone(a.clone())),
                            Term::TermId("⟇".to_string()),
                        ]
                    })
                    .flatten()
                    .collect::<Vec<_>>();
                terms_clause.pop(); //remove trailling ⟇

                // Prepare certificate
                let certificate = if ps.is_empty() {
                    ProofStep::Apply(Term::TermId(rule.to_string()), args)
                } else {
                    let mut tmp = vec![Term::TermId(rule.to_string())];
                    tmp.append(&mut ps);
                    ProofStep::Apply(Term::Terms(tmp), args)
                };

                ProofStep::Have(id.to_string(), Term::Terms(terms_clause), vec![certificate])
            }
            ProofCommand::Subproof(_) => todo!(),
        };
        steps.push(step);
    }

    // Conclude the proof
    let id_last_step = match proof_elaborated.commands.last().unwrap() {
        ProofCommand::Step(AstProofStep { id, .. }) => id,
        _ => unreachable!(),
    };

    steps.push(ProofStep::Apply(
        Term::TermId(id_last_step.to_string()),
        vec![],
    ));

    Proof(steps)
}

fn get_args(rule: &str, terms: &Vec<Rc<AletheTerm>>) -> Vec<Term> {
    let terms = terms
        .into_iter()
        .map(|t| Rc::unwrap_or_clone(t.clone()))
        .collect::<Vec<AletheTerm>>();
    match rule {
        "not_not" => match terms.as_slice() {
            [AletheTerm::Op(Operator::Not, _), e] => {
                vec![Term::from(e.clone())]
            }
            _ => unreachable!(),
        },
        "equiv_pos2" => match terms.as_slice() {
            [AletheTerm::Op(Operator::Not, e), _, _] => {
                let e = e
                    .into_iter()
                    .map(|t| Rc::unwrap_or_clone(t.clone()))
                    .collect::<Vec<AletheTerm>>();
                if let [AletheTerm::Op(Operator::Equals, e)] = e.as_slice() {
                    let e = e
                        .into_iter()
                        .map(|t| Rc::unwrap_or_clone(t.clone()))
                        .collect::<Vec<AletheTerm>>();
                    if let [e1, e2] = e.as_slice() {
                        vec![Term::from(e1.clone()), Term::from(e2.clone())]
                    } else {
                        unreachable!()
                    }
                } else {
                    unreachable!()
                }
            }
            _ => unreachable!(),
        },
        "or" => vec![],
        _ => unimplemented!(),
    }
}

// impl<A> Functor for Option<A> {
//     type Unwrapped = A;
//     type Wrapped<B> = Option<B>;

//     fn map<F: FnMut(A) -> B, B>(self, mut f: F) -> Option<B> {
//         match self {
//             Some(x) => Some(f(x)),
//             None => None,
//         }
//     }
// }

pub fn produce_lambdapi_proof(prelude: ProblemPrelude, proof_elaborated: ProofElaborated) {
    let mut header = header_modules();

    let mut prelude = export_prelude(prelude);

    // for h in header {
    //     println!("{}", h)
    // }

    for c in prelude {
        println!("{}", c)
    }

    let main_proof = Command::Symbol(
        Some(Modifier::Opaque),
        "proof_obligation".to_string(),
        vec![],
        Term::TermId("π ⊥".into()),
        Some(export_proof_step(proof_elaborated)),
    );

    println!("{}", main_proof)
}
