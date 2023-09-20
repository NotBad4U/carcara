#[allow(const_item_mutation)]
use crate::ast::{
    polyeq, Operator, ProblemPrelude, Proof as ProofElaborated, ProofArg, ProofCommand, ProofIter,
    ProofStep as AstProofStep, Rc, Sort, Term as AletheTerm,
};
use crate::ast::{BindingList, Quantifier, SortedVar};
use std::collections::VecDeque;
use std::fmt::{self};
use std::ops::Deref;
use std::time::Duration;
use std::vec;
use try_match::unwrap_match;

use itertools::Itertools;
use thiserror::Error;

#[inline]
fn TYPE() -> Term {
    Term::TermId("TYPE".into())
}

#[inline]
fn proof(term: Term) -> Term {
    Term::Alethe(LTerm::Proof(Box::new(term)))
}

#[derive(Debug, Error)]
pub enum TranslatorError {
    #[error("the pivot is not in the clause")]
    PivotNotInClause,
    #[error("the premises are incorrect")]
    PremisesError,
}

#[derive(Debug, Clone, PartialEq)]
struct SortedTerm(Box<Term>, Box<Term>);

impl From<&SortedVar> for SortedTerm {
    fn from(var: &SortedVar) -> Self {
        SortedTerm(
            Box::new(Term::TermId(var.0.clone())),
            Box::new(Term::from(&var.1)),
        )
    }
}

impl fmt::Display for SortedTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} : {}", self.0, self.1)
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Bindings(Vec<SortedTerm>);

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

impl fmt::Display for Bindings {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.iter().try_for_each(|s| write!(f, "s"))
    }
}

#[derive(Debug, Clone, PartialEq)]
enum LTerm {
    True,
    False,
    NAnd(Vec<Term>),
    NOr(Vec<Term>),
    Neg(Option<Box<Term>>), //TODO: explain why cong need to add Option to Neg
    Eq(Box<Term>, Box<Term>),
    Clauses(Vec<Term>),
    Proof(Box<Term>),
    Resolution(
        bool,
        Option<Box<Term>>,
        Option<Box<Term>>,
        Option<Box<Term>>,
        Box<Term>,
        Box<Term>,
    ),
    Forall(Bindings, Box<Term>),
    Exist(Bindings, Box<Term>),
}

impl fmt::Display for LTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LTerm::True => write!(f, "⊤"),
            LTerm::False => write!(f, "⊥"),
            LTerm::Neg(Some(t)) => write!(f, "¬ᶜ ({})", t),
            LTerm::Neg(None) => write!(f, "¬ᶜ"),
            LTerm::NAnd(ts) => {
                let s = Itertools::intersperse(
                    ts.into_iter().map(|t| format!("({})", t)),
                    " ∧ᶜ ".to_string(),
                )
                .collect::<String>();
                write!(f, "{}", s)
            }
            LTerm::NOr(ts) => {
                let s = Itertools::intersperse(
                    ts.into_iter().map(|t| format!("({})", t)),
                    " ∨ᶜ ".to_string(),
                )
                .collect::<String>();
                write!(f, "{}", s)
            }
            LTerm::Clauses(ts) => {
                if ts.is_empty() {
                    write!(f, "{}", LTerm::False)
                } else {
                    let s = Itertools::intersperse(
                        ts.into_iter().map(|t| format!("({})", t)),
                        " ⟇ ".to_string(),
                    )
                    .collect::<String>();
                    write!(f, "{}", s)
                }
            }
            LTerm::Eq(l, r) => {
                write!(f, "({}) = ({})", l, r)
            }
            LTerm::Proof(t) => write!(f, "π ({})", t),
            LTerm::Resolution(pivot_position, pivot, a, b, h1, h2) => {
                if *pivot_position {
                    write!(f, "resolutionₗ ")?;
                } else {
                    write!(f, "resolutionᵣ ")?;
                }

                write!(
                    f,
                    "{} {} {} {} {}",
                    pivot.to_owned().unwrap_or(Box::new(Term::Underscore)),
                    a.to_owned().unwrap_or(Box::new(Term::Underscore)),
                    b.to_owned().unwrap_or(Box::new(Term::Underscore)),
                    h1,
                    h2
                )
            }
            LTerm::Forall(bs, t) => write!(f, "`∀ᶜ {}, {}", bs, t),
            LTerm::Exist(bs, t) => write!(f, "`∃ᶜ {}, {}", bs, t),
        }
    }
}

type TradResult<T> = Result<T, TranslatorError>;

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
                write!(f, "\nend;")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Term {
    Alethe(LTerm),
    Sort(BuiltinSort),
    TermId(String),
    Terms(Vec<Term>),
    Applications(Vec<Term>),
    Underscore,
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::Alethe(t) => write!(f, "{}", t),
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

impl From<Operator> for Term {
    fn from(op: Operator) -> Self {
        match op {
            Operator::Not => Term::Alethe(LTerm::Neg(None)),
            Operator::Equals => Term::TermId("=".to_string()),
            Operator::Or => Term::TermId("∨".to_string()),
            o => todo!("Operator {:?}", o),
        }
    }
}

impl From<&Rc<AletheTerm>> for Term {
    fn from(term: &Rc<AletheTerm>) -> Self {
        match &**term {
            AletheTerm::Sort(sort) => match sort {
                Sort::Function(params) => {
                    Term::Applications(params.iter().map(Term::from).collect())
                }
                Sort::Atom(id, _terms) => Term::TermId(id.clone()),
                Sort::Bool => Term::Sort(BuiltinSort::Bool),
                s => todo!("{:#?}", s),
            },
            AletheTerm::App(f, args) => {
                let mut func = vec![Term::from(f)];
                let mut args: Vec<Term> = args.into_iter().map(Term::from).collect();
                func.append(&mut args);
                Term::Terms(func)
            }
            AletheTerm::Op(operator, args) => {
                let args = args.into_iter().map(Term::from).collect::<Vec<_>>();
                return match operator {
                    Operator::Not => Term::Alethe(LTerm::Neg(Some(Box::new(
                        args.first().map(|a| Term::from(a.clone())).unwrap(),
                    )))),
                    Operator::Or => Term::Alethe(LTerm::NOr(args)),
                    Operator::Equals => Term::Alethe(LTerm::Eq(
                        Box::new(args[0].clone()),
                        Box::new(args[1].clone()),
                    )),
                    Operator::And => Term::Alethe(LTerm::NAnd(args)),
                    o => todo!("Operator {:?}", o),
                };
            }
            AletheTerm::Lambda(..) => todo!("lambda term"),
            AletheTerm::Let(..) => todo!("let term"),
            AletheTerm::Quant(Quantifier::Forall, bs, t) => {
                Term::Alethe(LTerm::Forall(Bindings::from(bs), Box::new(Term::from(t))))
            }
            AletheTerm::Quant(Quantifier::Exists, bs, t) => {
                Term::Alethe(LTerm::Exist(Bindings::from(bs), Box::new(Term::from(t))))
            }
            AletheTerm::Var(id, _term) => Term::TermId(id.to_string()),
            e => todo!("{:#?}", e),
        }
    }
}

impl From<Rc<AletheTerm>> for Term {
    fn from(term: Rc<AletheTerm>) -> Self {
        Self::from(&term)
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
                steps.iter().for_each(|s| write!(f, "{}", s).unwrap());
                Ok(())
            }
        }
    }
}

#[derive(Debug, Clone)]
enum ProofStep {
    Assume(Vec<String>),
    Apply(Term, Vec<Term>, SubProofs),
    Refine(Term, Vec<Term>, SubProofs),
    Have(String, Term, Vec<ProofStep>), //TODO: change Vec<ProofStep> for Proof
    Admit,
    Reflexivity,
}

#[derive(Debug, Clone)]
struct SubProofs(Option<Vec<Proof>>);

impl fmt::Display for SubProofs {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let SubProofs(Some(ps)) = self {
            for p in ps.iter() {
                write!(f, "{{ {} }}", p)?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for ProofStep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ProofStep::Assume(ids) => {
                write!(
                    f,
                    "assume {};",
                    ids.iter()
                        .map(|e| format!("{}", e))
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
            ProofStep::Have(id, term, proof) => {
                let proof_steps_fmt: String = proof.iter().map(|p| format!("{}", p)).collect();
                let have_fmt = format!("have {} : {} {{ {} }};\n", id, term, proof_steps_fmt);
                write!(f, "{}", have_fmt)
            }
            ProofStep::Apply(t, args, subproofs) => {
                write!(f, "apply {}", t)?;

                if args.len() > 0 {
                    write!(
                        f,
                        " {}",
                        args.iter()
                            .map(|i| format!("{}", i))
                            .collect::<Vec<_>>()
                            .join(" ")
                    )?;
                }

                if let SubProofs(Some(sp)) = subproofs {
                    write!(f, " {}", SubProofs(Some(sp.to_vec())))?;
                }

                write!(f, ";")
            }
            ProofStep::Refine(t, args, subproofs) => {
                write!(
                    f,
                    "refine {} {} {};",
                    t,
                    args.iter()
                        .map(|i| format!("{}", i))
                        .collect::<Vec<_>>()
                        .join(" "),
                    subproofs
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
fn translate_prelude(prelude: ProblemPrelude) -> Vec<Command> {
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
        .map(|(id, term)| Command::Symbol(None, id.to_string(), vec![], Term::from(term), None))
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

fn translate_proof_step(proof_elaborated: ProofElaborated) -> Proof {
    let proof_iter: ProofIter = proof_elaborated.iter();
    let mut steps = vec![];

    for command in proof_elaborated.commands.iter() {
        let step = match command {
            ProofCommand::Assume { id, term } => ProofStep::Have(
                id.to_string(),
                proof(Term::from(term)),
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
                                        proof(Term::Alethe(LTerm::Clauses(
                                            remove_pivot_in_clause(
                                                &pivot.0,
                                                [h1.1.as_slice(), h2.1.as_slice()].concat(),
                                            )
                                            .into_iter()
                                            .map(|s| Term::from(s))
                                            .collect::<Vec<Term>>(),
                                        ))),
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
                                        proof(Term::Alethe(LTerm::Clauses(
                                            current_goal
                                                .iter()
                                                .map(|s| Term::from(s.clone()))
                                                .collect::<Vec<Term>>(),
                                        ))),
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

                steps.push(ProofStep::Refine(
                    Term::TermId(last_goal_name),
                    vec![],
                    SubProofs(None),
                ));

                ProofStep::Have(
                    id.to_string(),
                    proof(Term::Alethe(LTerm::Clauses(
                        clause.iter().map(|s| Term::from(s)).collect::<Vec<Term>>(),
                    ))),
                    steps,
                )
            }
            ProofCommand::Step(AstProofStep { id, clause, premises, rule, .. }) if rule == "or" => {
                // Convert clauses
                let terms = clause.into_iter().map(|a| Term::from(a)).collect();

                ProofStep::Have(
                    id.to_string(),
                    proof(Term::Alethe(LTerm::Clauses(terms))),
                    vec![ProofStep::Admit],
                )
            }
            ProofCommand::Step(AstProofStep {
                id,
                clause,
                premises: _,
                rule,
                args: _,
                discharge: _,
            }) if rule.contains("simp") => {
                let terms = clause.into_iter().map(|a| Term::from(a)).collect();

                ProofStep::Have(
                    id.to_string(),
                    proof(Term::Alethe(LTerm::Clauses(terms))),
                    vec![ProofStep::Admit],
                )
            }
            ProofCommand::Step(AstProofStep { id, clause, premises, rule, .. }) => {
                let premises: Vec<_> = get_premises_clause(&proof_iter, &premises);

                let clauses = clause.into_iter().map(|a| Term::from(a)).collect();

                // concat parameter and premises for the rule
                // Example:  `cong f t_i`, where f is the parameter function of the goal `f x = f y`
                // and the step t_i that is a proof of x = y
                let mut args = infer_args_from_clause(rule, clause);
                args.append(
                    &mut premises
                        .into_iter()
                        .map(|t| Term::TermId(t.0.into()))
                        .collect(),
                );

                let apply = ProofStep::Apply(translate_rule_name(rule), args, SubProofs(None));

                ProofStep::Have(
                    id.to_string(),
                    proof(Term::Alethe(LTerm::Clauses(clauses))),
                    vec![apply],
                )
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
        SubProofs(None),
    ));

    Proof(steps)
}

pub fn produce_lambdapi_proof(prelude: ProblemPrelude, proof_elaborated: ProofElaborated) {
    let header = header_modules();

    let prelude = translate_prelude(prelude);

    for c in prelude {
        println!("{}", c)
    }

    let main_proof = Command::Symbol(
        Some(Modifier::Opaque),
        "proof_obligation".to_string(),
        vec![],
        Term::TermId("π ⊥".into()),
        Some(translate_proof_step(proof_elaborated)),
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
            Direction::Left => {
                ProofStep::Apply(Term::TermId("⟇ᵢ₁".into()), vec![], SubProofs(None))
            }
            Direction::Right => {
                ProofStep::Apply(Term::TermId("⟇ᵢ₂".into()), vec![], SubProofs(None))
            }
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
/// TODO: update name
fn get_path_of_pivot_in_clause(
    pivot: &Rc<AletheTerm>,
    terms: &[Rc<AletheTerm>],
) -> TradResult<Vec<Direction>> {
    let mut path = Vec::new();
    if terms.len() > 2 {
        let position = terms
            .iter()
            .position(|e| polyeq(e, pivot, &mut Duration::ZERO))
            .ok_or(TranslatorError::PivotNotInClause)?;
        path = itertools::repeat_n(Direction::Right, position).collect::<Vec<Direction>>();

        if position != terms.len() - 1 {
            path.push(Direction::Left);
        }
    } else {
        if polyeq(pivot, terms.first().unwrap(), &mut Duration::ZERO) {
            path.push(Direction::Left);
        } else {
            path.push(Direction::Right);
        };
    }
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
            polyeq(term, t, &mut Duration::ZERO) == false
                && polyeq(&term_negated(term), t, &mut Duration::ZERO) == false
        })
        .collect()
}

fn make_resolution(
    (pivot, flag_position_pivot): &(Rc<AletheTerm>, bool),
    (left_step_name, left_clause): &(&str, &[Rc<AletheTerm>]),
    (right_step_name, right_clause): &(&str, &[Rc<AletheTerm>]),
) -> Vec<ProofStep> {
    let mut steps = vec![];
    let mut hyp_left_arg = Term::TermId(left_step_name.to_string());
    let mut hyp_right_arg = Term::TermId(right_step_name.to_string());

    if flag_position_pivot.to_owned() {
        // Pivot is in the left clause
        if term_at_head_of_clause(pivot, left_clause) == false {
            steps.push(move_pivot_lemma(
                format!("{}'", left_step_name).as_str(),
                pivot,
                left_clause,
            ));
            hyp_left_arg = Term::Terms(vec![
                Term::TermId(format!("{}'", left_step_name)),
                Term::TermId(left_step_name.to_string()),
            ]);
        }
        if term_at_head_of_clause(&term_negated(pivot), right_clause) == false {
            steps.push(move_pivot_lemma(
                format!("{}'", right_step_name).as_str(),
                &term_negated(pivot),
                right_clause,
            ));
            Term::Terms(vec![
                Term::TermId(format!("{}'", right_step_name)),
                Term::TermId(right_step_name.to_string()),
            ]);
        }
    } else {
        // Pivot is in the right clause
        if term_at_head_of_clause(&term_negated(pivot), left_clause) == false {
            steps.push(move_pivot_lemma(
                format!("{}'", left_step_name).as_str(),
                &term_negated(pivot),
                left_clause,
            ));
            hyp_left_arg = Term::Terms(vec![
                Term::TermId(format!("{}'", left_step_name)),
                Term::TermId(left_step_name.to_string()),
            ]);
        }
        if term_at_head_of_clause(pivot, right_clause) == false {
            steps.push(move_pivot_lemma(
                format!("{}'", right_step_name).as_str(),
                pivot,
                right_clause,
            ));
            hyp_right_arg = Term::Terms(vec![
                Term::TermId(format!("{}'", right_step_name)),
                Term::TermId(right_step_name.to_string()),
            ]);
        }
    };

    if left_clause.len() == 1 {
        hyp_left_arg = Term::Terms(vec![
            Term::TermId("@⟇ᵢ₁".to_string()),
            Term::Underscore,
            Term::Alethe(LTerm::False),
            hyp_left_arg,
        ])
    }
    if right_clause.len() == 1 {
        hyp_right_arg = Term::Terms(vec![
            Term::TermId("@⟇ᵢ₁".to_string()),
            Term::Underscore,
            Term::Alethe(LTerm::False),
            hyp_right_arg,
        ])
    }

    let resolution = LTerm::Resolution(
        *flag_position_pivot,
        None,
        None,
        None,
        Box::new(hyp_left_arg),
        Box::new(hyp_right_arg),
    );

    steps.push(ProofStep::Apply(
        Term::Alethe(resolution),
        vec![],
        SubProofs(None),
    ));
    steps
}

fn term_negated(term: &Rc<AletheTerm>) -> Rc<AletheTerm> {
    Rc::from(AletheTerm::Op(Operator::Not, vec![Rc::from(term.clone())]))
}

fn term_at_head_of_clause(term: &Rc<AletheTerm>, terms: &[Rc<AletheTerm>]) -> bool {
    terms.len() > 0 && polyeq(term, &terms[0], &mut Duration::ZERO)
}

/// Generate a sublemma to move the pivot. Consider the pivot `x` and the clause (cl a b (not x) c)
/// this function will create the sublemma step to move the pivot:
/// have move_head_notx: Prf((a ⟇ b ⟇ x ⟇ c)  →  (x ⟇ a ⟇ b ⟇ c))  {
///     [proof generated here]
/// }
fn move_pivot_lemma(name: &str, pivot: &Rc<AletheTerm>, clause: &[Rc<AletheTerm>]) -> ProofStep {
    let pivot_tr: Term = Term::from(pivot.clone());

    //FIXME: avoid to clone twice the clause
    let previous_clause: Vec<_> = clause.into_iter().map(|t| Term::from(t.clone())).collect();

    let mut new_clause: VecDeque<_> = clause
        .into_iter()
        .map(|t| Term::from(t))
        .filter(|t| *t != pivot_tr)
        .collect();
    new_clause.push_front(pivot_tr.clone());

    let mut new_clause2: VecDeque<Rc<AletheTerm>> = clause
        .into_iter()
        .filter(|t| polyeq(pivot, t, &mut Duration::ZERO) == false)
        .map(|t| t.clone())
        .collect();
    new_clause2.push_front(pivot.clone());
    new_clause2.make_contiguous();

    let proof_script = foo(clause, new_clause2.as_slices().0).0;

    ProofStep::Have(
        format!("{}", name),
        Term::Terms(vec![
            proof(Term::Alethe(LTerm::Clauses(previous_clause))),
            Term::TermId("→".into()),
            proof(Term::Alethe(LTerm::Clauses(new_clause.into()))),
        ]),
        proof_script,
    )
}

fn foo(clauses: &[Rc<AletheTerm>], new_clauses: &[Rc<AletheTerm>]) -> Proof {
    let current_hyp_name = format!("H{}", clauses.len());

    if clauses.len() == 1 {
        let mut proof_find_elem = vec![];
        let path = get_path_of_pivot_in_clause(clauses.first().unwrap(), new_clauses).unwrap();
        let mut path_proof = convert_path_into_proofstep(path);

        proof_find_elem.push(ProofStep::Assume(vec![current_hyp_name.clone()]));
        proof_find_elem.append(&mut path_proof);
        proof_find_elem.push(ProofStep::Apply(
            Term::TermId(current_hyp_name),
            vec![],
            SubProofs(None),
        ));

        Proof(proof_find_elem)
    } else {
        let mut proof_find_elem = vec![];
        let path = get_path_of_pivot_in_clause(clauses.first().unwrap(), new_clauses).unwrap();
        let mut path_proof = convert_path_into_proofstep(path);

        proof_find_elem.push(ProofStep::Assume(vec!["H".to_string()]));
        proof_find_elem.append(&mut path_proof);
        proof_find_elem.push(ProofStep::Apply(
            Term::TermId("H".to_string()),
            vec![],
            SubProofs(None),
        ));

        Proof(vec![
            ProofStep::Assume(vec![current_hyp_name.clone()]),
            ProofStep::Apply(
                Term::TermId("⟇ₑ".to_string()),
                vec![Term::TermId(current_hyp_name)],
                SubProofs(Some(vec![
                    Proof(proof_find_elem),
                    foo(&clauses[1..clauses.len()], new_clauses),
                ])),
            ),
        ])
    }
}

fn infer_args_from_clause(rule: &str, clause: &[Rc<AletheTerm>]) -> Vec<Term> {
    match rule {
        "cong" => {
            unwrap_match!(clause[0].deref(), AletheTerm::Op(Operator::Equals, ts) => {
                match (&*ts[0], &*ts[1]) {
                    (AletheTerm::App(f, _) , AletheTerm::App(g, _)) if f == g => vec![Term::from((*f).clone())],
                    (AletheTerm::Op(f, _) , AletheTerm::Op(g, _)) if f == g => vec![Term::from(*f)],
                    _ => unreachable!()
                }
            })
        }
        "trans" => vec![],
        _ => vec![],
    }
}

fn translate_rule_name(rule: &str) -> Term {
    match rule {
        "cong" => Term::TermId("feq".to_string()),
        "trans" => Term::TermId("=_trans".to_string()),
        r => Term::TermId(r.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use crate::{ast::ProofCommand, checker, checker::Config, parser};
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

        let (prelude, proof, mut pool) = parser::parse_instance(
            Cursor::new(definitions),
            Cursor::new(proof),
            parser::Config::default(),
        )
        .expect("parse proof and definition");

        let mut checker = checker::ProofChecker::new(&mut pool, Config::new(), &prelude);
        let (_, elaborated) = checker.check_and_elaborate(proof).unwrap();

        if let [t1, t2, t3, ..] = elaborated.commands.as_slice() {
            let (_, t2, t3) = match (t1, t2, t3) {
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

        let (prelude, proof, mut pool) = parser::parse_instance(
            Cursor::new(definitions),
            Cursor::new(proof),
            parser::Config::default(),
        )
        .expect("parse proof and definition");

        let mut checker = checker::ProofChecker::new(&mut pool, Config::new(), &prelude);
        let (_, elaborated) = checker.check_and_elaborate(proof).unwrap();

        let res = super::translate_proof_step(elaborated);

        println!("{}", res);
    }
}
