#[allow(const_item_mutation)]
use crate::ast::{
    deep_eq, Identifier, Operator, ProblemPrelude, Proof as ProofElaborated, ProofArg,
    ProofCommand, ProofIter, ProofStep as AstProofStep, Rc, Sort, Term as AletheTerm, Terminal,
};
use itertools::Itertools;
use std::collections::VecDeque;
use std::fmt::{self};
use std::time::Duration;
use std::vec;

use thiserror::Error;

#[derive(Debug, Error)]
pub enum TranslatorError {
    #[error("the pivot is not in the clause")]
    PivotNotInClause,
    #[error("the premises are incorrect")]
    PremisesError,
}

type TradResult<T> = Result<T, TranslatorError>;

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
    Underscore,
}

// struct Clauses(Vec<Term>);

// impl fmt::Display for Clauses {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         let ts: String = intersperse(self.0.clone(), Term::TermId("⟇".to_string()))
//             .map(|e| format!("{}", e))
//             .collect::<Vec<_>>()
//             .join(" ");
//         write!(f, "{}", ts)
//     }
// }

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
            Term::Underscore => write!(f, "_"),
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
                Sort::Atom(id, _terms) => Term::TermId(id),
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
    Resolution(Option<Term>, Option<Term>, Option<Term>, Term, Term),
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
                    "apply {} {};",
                    t,
                    args.iter()
                        .map(|i| format!("{}", i))
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
            ProofStep::Admit => write!(f, "admit;"),
            ProofStep::Reflexivity => write!(f, "simplify; reflexivity;"),
            ProofStep::Resolution(pivot, a, b, h1, h2) => {
                write!(
                    f,
                    "apply resolution {} {} {} {} {};",
                    pivot.to_owned().unwrap_or(Term::Underscore),
                    a.to_owned().unwrap_or(Term::Underscore),
                    b.to_owned().unwrap_or(Term::Underscore),
                    h1,
                    h2
                )
            }
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

fn empty_clause(ts: Vec<Term>) -> Vec<Term> {
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
                let premises = get_premises_clause(&proof_iter, &premises);

                let pivots = get_pivots_from_args(args);

                let (last_goal_name, _, mut steps) = match premises.as_slice() {
                    [h1, h2, tl_premises @ ..] => match pivots.as_slice() {
                        [pivot, tl_pivot @ ..] => {
                            tl_premises.into_iter().zip(tl_pivot.into_iter()).fold(
                                (
                                    format!("{}_{}", h1.0, h2.0),
                                    remove_pivot_in_clause(
                                        &pivot.0,
                                        [h1.1.as_slice(), h2.1.as_slice()].concat(),
                                    ),
                                    vec![ProofStep::Have(
                                        format!("{}_{}", h1.0, h2.0),
                                        Term::Terms(
                                            remove_pivot_in_clause(
                                                &pivot.0,
                                                [h1.1.as_slice(), h2.1.as_slice()].concat(),
                                            )
                                            .into_iter()
                                            .map(|s| Term::from(Rc::unwrap_or_clone(s)))
                                            .collect::<Vec<Term>>(),
                                        ),
                                        make_resolution(
                                            pivot,
                                            &(h1.0, h1.1.as_slice()),
                                            &(h2.0, h2.1.as_slice()),
                                        ),
                                    )],
                                ),
                                |(previous_goal_name, previous_goal, mut proof_steps),
                                 (premise, pivot)| {
                                    let goal_name = format!("{}_{}", previous_goal_name, premise.0);

                                    let current_goal = remove_pivot_in_clause(
                                        &pivot.0,
                                        [previous_goal.as_slice(), premise.1.as_slice()].concat(),
                                    );

                                    let resolution = make_resolution(
                                        pivot,
                                        &(
                                            format!("{}", previous_goal_name).as_str(),
                                            &previous_goal,
                                        ),
                                        &(premise.0, premise.1.as_slice()),
                                    );

                                    proof_steps.push(ProofStep::Have(
                                        goal_name.clone(),
                                        Term::Terms(
                                            current_goal
                                                .iter()
                                                .map(|s| Term::from(Rc::unwrap_or_clone(s.clone())))
                                                .collect::<Vec<Term>>(),
                                        ),
                                        resolution,
                                    ));

                                    (goal_name, current_goal, proof_steps)
                                },
                            )
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                };

                steps.push(ProofStep::Apply(Term::TermId(last_goal_name), vec![]));

                ProofStep::Have(
                    id.to_string(),
                    Term::Terms(
                        clause
                            .iter()
                            .map(|s| Term::from(Rc::unwrap_or_clone(s.clone())))
                            .collect::<Vec<Term>>(),
                    ),
                    steps,
                )
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
                    ProofStep::Apply(Term::TermId(rule.to_string()), vec![])
                } else {
                    let mut tmp = vec![Term::TermId(rule.to_string())];
                    tmp.append(&mut ps);
                    ProofStep::Apply(Term::Terms(tmp), vec![])
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

pub fn produce_lambdapi_proof(prelude: ProblemPrelude, proof_elaborated: ProofElaborated) {
    let mut header = header_modules();

    let mut prelude = export_prelude(prelude);

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

fn get_premises_clause<'a>(
    proof_iter: &'a ProofIter,
    premises: &'a [(usize, usize)],
) -> Vec<(&'a str, Vec<Rc<AletheTerm>>)> {
    premises
        .into_iter()
        .map(|p| match proof_iter.get_premise(*p) {
            ProofCommand::Assume { id, term } => (id.as_str(), vec![(*term).clone()]),
            ProofCommand::Step(AstProofStep { id, clause, .. }) => (id.as_str(), (*clause).clone()),
            _ => unreachable!(),
        })
        .collect()
}

fn get_pivots_from_args(args: &[ProofArg]) -> Vec<(Rc<AletheTerm>, bool)> {
    args.into_iter()
        .tuples()
        .map(|(x, y)| match (x, y) {
            (ProofArg::Term(pivot), ProofArg::Term(flag)) if flag.is_bool_true() => {
                ((*pivot).clone(), true)
            }
            (ProofArg::Term(pivot), ProofArg::Term(flag)) if flag.is_bool_false() => {
                ((*pivot).clone(), false)
            }
            _ => panic!("Pivot are not a tuple of term and bool anymore"),
        })
        .collect_vec()
}

/// Represent the path directions of pivot in a clause.
#[derive(Clone, Debug, PartialEq)]
enum Direction {
    Left,
    Right,
}

/// Convert a Vec<Direction> into a Vec<ProofStep>
/// For example, a path Right :: Right :: Left is converted into
/// [ apply right; apply right; apply left; ]
fn convert_path_into_proofstep(path: Vec<Direction>) -> Vec<ProofStep> {
    path.into_iter()
        .map(|d| match d {
            Direction::Left => ProofStep::Apply(Term::TermId("left".into()), vec![]),
            Direction::Right => ProofStep::Apply(Term::TermId("right".into()), vec![]),
        })
        .collect()
}

/// Construct the path where the pivot is in the clause.
/// Clause are a binary disjunction tree represented as a [Rc<Term>].
///
/// Let `x` be our pivot and considering the clause a ⟇ ( b ⟇ ( x ⟇ ( c ⟇ d ) ) )
/// represented by the slice [a, b, x, c, d], the path of `x` is Right :: Right :: Left
///
/// NOTE: A similar approach could have be done with a Zipper, but the implementation would have be
/// unnecessary difficult due to Vec ownership.
///
/// This function should only be call if the pivot is not at the head of the clause otherwise it will panic.
fn get_path_of_pivot_in_clause(
    pivot: &Rc<AletheTerm>,
    terms: &[Rc<AletheTerm>],
) -> TradResult<Vec<Direction>> {
    let position = terms
        .into_iter()
        .position(|e| deep_eq(e, pivot, &mut Duration::ZERO))
        .ok_or(TranslatorError::PivotNotInClause)?;

    let mut path = itertools::repeat_n(Direction::Right, position).collect::<Vec<Direction>>();
    path.push(Direction::Left);

    Ok(path)
}

/// Remove the pivot and its negation form in a clause.
fn remove_pivot_in_clause<'a>(
    term: &Rc<AletheTerm>,
    terms: Vec<Rc<AletheTerm>>,
) -> Vec<Rc<AletheTerm>> {
    terms
        .into_iter()
        .filter(|t| {
            deep_eq(term, t, &mut Duration::ZERO) == false
                && deep_eq(&term_negated(term), t, &mut Duration::ZERO) == false
        })
        .collect()
}

fn make_resolution(
    (pivot, flag_position_pivot): &(Rc<AletheTerm>, bool),
    (left_step_name, left_clause): &(&str, &[Rc<AletheTerm>]),
    (right_step_name, right_clause): &(&str, &[Rc<AletheTerm>]),
) -> Vec<ProofStep> {
    let mut steps = vec![];
    let (mut pivot_moved, mut neg_pivot_moved) = (false, false);

    if flag_position_pivot.to_owned() {
        // Pivot is in the left clause
        if term_at_head_of_clause(pivot, left_clause) == false {
            steps.push(move_pivot_lemma(
                format!("{}'", left_step_name).as_str(),
                pivot,
                left_clause,
            ));
            pivot_moved = true;
        }
        if term_at_head_of_clause(&term_negated(pivot), right_clause) == false {
            steps.push(move_pivot_lemma(
                format!("{}'", right_step_name).as_str(),
                &term_negated(pivot),
                right_clause,
            ));
            neg_pivot_moved = true;
        }
    } else {
        // Pivot is in the right clause
        if term_at_head_of_clause(&term_negated(pivot), left_clause) == false {
            steps.push(move_pivot_lemma(
                format!("{}'", left_step_name).as_str(),
                &term_negated(pivot),
                left_clause,
            ));
            neg_pivot_moved = true;
        }
        if term_at_head_of_clause(pivot, right_clause) == false {
            steps.push(move_pivot_lemma(
                format!("{}'", right_step_name).as_str(),
                pivot,
                right_clause,
            ));
            pivot_moved = true;
        }
    };

    let resolution = match (pivot_moved, neg_pivot_moved) {
        (true, true) => ProofStep::Resolution(
            None,
            None,
            None,
            Term::Terms(vec![
                Term::TermId(format!("{}'", left_step_name)),
                Term::TermId(left_step_name.to_string()),
            ]),
            Term::Terms(vec![
                Term::TermId(format!("{}'", right_step_name)),
                Term::TermId(right_step_name.to_string()),
            ]),
        ),
        (true, false) => ProofStep::Resolution(
            None,
            None,
            None,
            Term::Terms(vec![
                Term::TermId(format!("{}'", left_step_name)),
                Term::TermId(left_step_name.to_string()),
            ]),
            Term::TermId(right_step_name.to_string()),
        ),
        (false, true) => ProofStep::Resolution(
            None,
            None,
            None,
            Term::TermId(left_step_name.to_string()),
            Term::Terms(vec![
                Term::TermId(format!("{}'", right_step_name)),
                Term::TermId(right_step_name.to_string()),
            ]),
        ),
        (_, _) => ProofStep::Resolution(
            None,
            None,
            None,
            Term::TermId(left_step_name.to_string()),
            Term::TermId(right_step_name.to_string()),
        ),
    };

    steps.push(resolution);
    steps
}

fn term_negated(term: &Rc<AletheTerm>) -> Rc<AletheTerm> {
    Rc::from(AletheTerm::Op(Operator::Not, vec![Rc::from(term.clone())]))
}

fn term_at_head_of_clause(term: &Rc<AletheTerm>, terms: &[Rc<AletheTerm>]) -> bool {
    terms.len() > 0 && deep_eq(term, &terms[0], &mut Duration::ZERO)
}

/// Generate a sublemma to move the pivot. Consider the pivot `x` and the clause (cl a b (not x) c)
/// this function will create the sublemma step to move the pivot:
/// have move_head_notx: Prf((a ⟇ b ⟇ x ⟇ c)  →  (x ⟇ a ⟇ b ⟇ c))  {
///     [proof generated here]
/// }
fn move_pivot_lemma(name: &str, pivot: &Rc<AletheTerm>, clause: &[Rc<AletheTerm>]) -> ProofStep {
    let pivot_tr: Term = Term::from(Rc::unwrap_or_clone(pivot.to_owned()));

    //FIXME: avoid to clone twice the clause
    let previous_clause: Vec<_> = clause
        .into_iter()
        .map(|t| Term::from(Rc::unwrap_or_clone(t.to_owned())))
        .collect();

    let mut new_clause: VecDeque<_> = clause
        .into_iter()
        .map(|t| Term::from(Rc::unwrap_or_clone(t.to_owned())))
        .filter(|t| *t != pivot_tr)
        .collect();
    new_clause.push_front(pivot_tr.clone());

    ProofStep::Have(
        format!("{}", name),
        Term::Terms(vec![
            Term::Terms(previous_clause),
            Term::TermId("→".into()),
            Term::Terms(new_clause.into()),
        ]),
        vec![ProofStep::Admit],
    )
}

#[cfg(test)]
mod tests {
    use crate::{ast::ProofCommand, checker, checker::Config, parser::parse_instance};
    use std::io::Cursor;

    use super::get_pivots_from_args;
    #[test]
    fn test_translate_path_pivot() {
        let definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
            (declare-fun t () Bool)
            (declare-fun u () Bool)
            (declare-fun v () Bool)
        ";

        let proof = "
        (step t1 (cl (not p) r s t) :rule hole)
        (step t2 (cl q u p v) :rule hole)
        (step t3 (cl r s t q u v) :rule resolution :premises (t1 t2))
        (step tf (cl ) :rule hole :premises (t1 t2 t3))";

        let (prelude, proof, mut pool) = parse_instance(
            Cursor::new(definitions),
            Cursor::new(proof),
            true,
            false,
            false,
        )
        .expect("parse proof and definition");

        let mut checker = checker::ProofChecker::new(&mut pool, Config::new(), prelude);
        let (is_holey, elaborated) = checker.check_and_elaborate(proof).unwrap();

        if let [t1, t2, t3, ..] = elaborated.commands.as_slice() {
            let (t1, t2, t3) = match (t1, t2, t3) {
                (ProofCommand::Step(t1), ProofCommand::Step(t2), ProofCommand::Step(t3)) => {
                    (t1, t2, t3)
                }
                _ => panic!(),
            };

            let pivot = get_pivots_from_args(&t3.args).first().unwrap().clone();

            let path = super::get_path_of_pivot_in_clause(&pivot.0, t2.clause.as_slice()).unwrap();
            assert!(path.len() == 3);
            let converted_path = super::convert_path_into_proofstep(path);
            assert!(converted_path.len() == 3);
        } else {
            panic!();
        }
    }

    #[test]
    fn test_translate_resolution() {
        let definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
            (declare-fun t () Bool)
            (declare-fun u () Bool)
            (declare-fun v () Bool)
            (declare-fun x () Bool)
        ";

        let proof = "
        (step t1 (cl r (not p) s) :rule hole)
        (step t2 (cl q u p) :rule hole)
        (step t3 (cl (not q) t v) :rule hole)
        (step t4 (cl x (not u)) :rule hole)
        (step t5 (cl r s t v x) :rule resolution :premises (t1 t2 t3 t4))
        (step tf (cl ) :rule hole :premises (t1 t2 t3 t4 t5))";

        let (prelude, proof, mut pool) = parse_instance(
            Cursor::new(definitions),
            Cursor::new(proof),
            true,
            false,
            false,
        )
        .expect("parse proof and definition");

        let mut checker = checker::ProofChecker::new(&mut pool, Config::new(), prelude);
        let (is_holey, elaborated) = checker.check_and_elaborate(proof).unwrap();

        let res = super::export_proof_step(elaborated);

        println!("{}", res);
    }
}
