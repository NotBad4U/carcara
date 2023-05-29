use crate::ast::{
    Identifier, Operator, ProblemPrelude, Proof as ProofElaborated, ProofCommand, ProofIter,
    ProofStep as AstProofStep, Rc, Sort, Term as AstTerm, Terminal,
};
use std::fmt;

static ASCII_LOWER: [char; 26] = [
    'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's',
    't', 'u', 'v', 'w', 'x', 'y', 'z',
];

#[inline]
fn prop() -> Term {
    Term::TermId("Prop".into())
}
#[inline]
fn set() -> Term {
    Term::TermId("Set".into())
}

#[inline]
fn TYPE() -> Term {
    Term::TermId("TYPE".into())
}

#[inline]
fn π(prop: Term) -> Term {
    Term::Terms(vec![Term::TermId("π".into()), prop])
}

#[inline]
fn bottom() -> Term {
    Term::TermId("⊥".into())
}

#[derive(Debug, Clone)]
enum BuiltinSort {
    Bool,
}

impl fmt::Display for BuiltinSort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BuiltinSort::Bool => write!(f, "𝔹"),
        }
    }
}

#[derive(Debug, Clone)]
enum Modifier {
    Constant,
    Injective,
    Opaque,
}

impl fmt::Display for Modifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Modifier::Constant => write!(f, "constant"),
            Modifier::Injective => write!(f, "injective"),
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

#[derive(Debug, Clone)]
enum Term {
    Sort(BuiltinSort),
    TermId(String),
    Terms(Vec<Term>),
    Lambda(Box<BinderAnonymous>),
    ProdTerm(Box<Binder>),
    Application(Box<Term>, Box<Term>),
    Applications(Vec<Term>),
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

impl From<AstTerm> for Term {
    fn from(term: AstTerm) -> Self {
        match term {
            AstTerm::Sort(sort) => match sort {
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
            AstTerm::App(f, args) => {
                let mut func = vec![Term::from(Rc::unwrap_or_clone(f))];
                let mut args: Vec<Term> = args
                    .into_iter()
                    .map(|a| Term::from(Rc::unwrap_or_clone(a)))
                    .collect();
                func.append(&mut args);
                Term::Terms(func)
            }
            AstTerm::Op(operator, args) => match operator {
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
                    let right = Term::from(Rc::unwrap_or_clone(args[0].clone()));

                    Term::Terms(vec![left, Term::TermId("=".to_string()), right])
                }
                o => todo!("missing operator {}", o),
            },
            AstTerm::Lambda(..) => todo!("lambda"),
            AstTerm::Let(..) => todo!("let"),
            AstTerm::Terminal(terminal) => match terminal {
                Terminal::String(id) => Term::TermId(id),
                Terminal::Var(Identifier::Simple(id), ..) => Term::TermId(id),
                t => todo!("{:#?}", t),
            },
            e => todo!("{:#?}", e),
        }
    }
}

#[derive(Debug, Clone)]
struct BinderAnonymous {
    param: Vec<String>,
    term: Term,
}

#[derive(Debug, Clone)]
struct Binder {
    param: (String, Term),
    term: Term,
}

#[derive(Debug, Clone)]
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
    Assume(Vec<String>),
    Apply(Term),
    Have(String, Term, Box<ProofStep>),
    Admit,
    Simplify,
}

impl fmt::Display for ProofStep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ProofStep::Assume(ids) => {
                write!(
                    f,
                    "assume {}",
                    ids.iter()
                        .map(|i| format!("{}", i))
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
            ProofStep::Have(id, term, proof) => {
                writeln!(f, "have {} : π {} {{", id, term)?;
                writeln!(f, "\t{}", proof)?;
                write!(f, "}};")
            }
            ProofStep::Apply(t) => write!(f, "apply {};", t),
            ProofStep::Admit => write!(f, "admit;"),
            ProofStep::Simplify => write!(f, "simplify;"),
        }
    }
}

// impl From<ProofCommand> for ProofStep {
//     fn from(term: ProofCommand) -> Self {
//         match term {
//             ProofCommand::Assume { id, term } => ProofStep::Have(
//                 id,
//                 Term::from(Rc::unwrap_or_clone(term)),
//                 Box::new(ProofStep::Admit),
//             ),
//             ProofCommand::Step(AstProofStep {
//                 id,
//                 clause,
//                 premises,
//                 rule,
//                 args,
//                 discharge,
//             }) => {
//                 todo!("{:#?}", premises)
//                 // ProofStep::Have(
//                 //     id,

//                 //)
//             },
//             ProofCommand::Subproof(_) => todo!(),
//             _ => todo!(),
//         }
//     }
// }

/// Alethe rules
// enum Rule {
//     not_equiv1,
//     not_not,
//     resolution,
//     ac_simp,
// }

trait Functor {
    type Unwrapped;
    type Wrapped<B>: Functor;

    fn map<F, B>(self, f: F) -> Self::Wrapped<B>
    where
        F: FnMut(Self::Unwrapped) -> B;
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

fn export_proof_step(proof_elaborated: ProofElaborated) -> Proof {
    let proof_iter: ProofIter = proof_elaborated.iter();
    let mut steps = vec![];

    for command in proof_elaborated.commands.iter() {
        let step = match command {
            ProofCommand::Assume { id, term } => ProofStep::Have(
                id.to_string(),
                Term::from(Rc::unwrap_or_clone(term.clone())),
                Box::new(ProofStep::Admit),
            ),
            ProofCommand::Step(AstProofStep {
                id,
                clause,
                premises,
                rule,
                args,
                discharge,
            }) if rule == "resolution" || rule == "th_resolution" => {
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

                ProofStep::Have(id.to_string(), clause, Box::new(ProofStep::Admit))
            }
            ProofCommand::Step(AstProofStep {
                id,
                clause,
                premises,
                rule,
                args,
                discharge,
            }) => {
                let mut ps: Vec<String> = Vec::new();

                if premises.len() > 0 {
                    ps = premises
                        .iter()
                        .map(|p| match proof_iter.get_premise(*p) {
                            ProofCommand::Assume { id, .. } => id.clone(),
                            ProofCommand::Step(AstProofStep { id, .. }) => id.clone(),
                            _ => unreachable!(),
                        })
                        .collect();
                }
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
                    Box::new(ProofStep::Admit),
                )
            }
            ProofCommand::Subproof(_) => todo!(),
        };
        steps.push(step);
    }


    // Conclude the proof
    let id_last_step = match proof_elaborated.commands.last().unwrap() {
        ProofCommand::Step(AstProofStep{id,..}) => id,
        _ => unreachable!(),
    };

    steps.push(ProofStep::Apply(Term::TermId(id_last_step.to_string())));

    Proof(steps)
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

    for h in header {
        println!("{}", h)
    }

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
