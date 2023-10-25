#[allow(const_item_mutation)]
use crate::ast::{
    polyeq, Operator, ProblemPrelude, Proof as ProofElaborated, ProofArg, ProofCommand, ProofIter,
    ProofStep as AstProofStep, Rc, Sort, Subproof, Term as AletheTerm,
};
use crate::ast::{BindingList, Ident, Quantifier, SortedVar};
use crate::parser::FunctionDef;
use indexmap::IndexMap;
use std::collections::VecDeque;
use std::fmt;
use std::ops::Deref;
use std::time::Duration;
use try_match::unwrap_match;

use itertools::Itertools;
use thiserror::Error;

use self::printer::PrettyPrint;

pub mod printer;

/// The BNF grammar of Lambdapi is in [lambdapi.bnf](https://raw.githubusercontent.com/Deducteam/lambdapi/master/doc/lambdapi.bnf).
/// Data structure of this file try to represent this grammar.

const WHITE_SPACE: &'static str = " ";

#[inline]
#[allow(non_snake_case)]
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
pub struct SortedTerm(Box<Term>, Box<Term>);

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
        write!(f, "{}: {}", self.0, self.1)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Bindings(Vec<SortedTerm>);

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
        let s = Itertools::intersperse(
            self.0.iter().map(|t| format!("({})", t)),
            WHITE_SPACE.to_string(),
        )
        .collect::<String>();
        write!(f, "{}", s)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum LTerm {
    True,
    False,
    NAnd(Vec<Term>),
    NOr(Vec<Term>),
    Neg(Option<Box<Term>>), //TODO: explain why cong need to add Option to Neg
    Implies(Box<Term>, Box<Term>),
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
            LTerm::Implies(l, r) => {
                write!(f, "({}) ⟹ᶜ ({})", l, r)
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

pub type TradResult<T> = Result<T, TranslatorError>;

#[derive(Debug, Clone, PartialEq)]
pub enum BuiltinSort {
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

/// Lambdapi files are formed of a list of commands.
#[derive(Default)]
pub struct LambdapiFile(pub VecDeque<Command>);

impl fmt::Display for LambdapiFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.render_fmt(f)
    }
}

impl LambdapiFile {
    #[inline]
    fn extend(&mut self, cs: Vec<Command>) {
        self.0.extend(cs)
    }

    #[inline]
    fn push_back(&mut self, cs: Command) {
        self.0.push_back(cs)
    }
}

/// The Grammar <command> token
#[derive(Debug, Clone)]
pub enum Command {
    RequireOpen(String),
    /// <modifier>* "symbol" <uid_or_nat> <param_list>* ":" <term> [<proof>] ";"
    Symbol(Option<Modifier>, String, Vec<Param>, Term, Option<Proof>),
    /// Simplification of command case: <modifier>* "symbol" <uid_or_nat> <param_list>* [":" <term>] "≔" <term_proof> ";"
    Definition(String, Term),
    Rule(Term, Term),
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
                        .map(|m| format!("{} ", m))
                        .unwrap_or(String::new()),
                    name,
                    params,
                    term
                )?;

                if let Some(proof) = proof {
                    write!(f, " ≔\n")?;
                    writeln!(f, "begin")?;
                    write!(f, "{}", proof)?;
                    write!(f, "\nend")?;
                }
                write!(f, ";\n")
            }
            Command::Definition(name, term) => {
                writeln!(f, "symbol {} ≔ {};", name, term)
            }
            Command::Rule(l, r) => writeln!(f, "rule {} ↪ {};", l, r),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Alethe(LTerm),
    Sort(BuiltinSort),
    TermId(String),
    Terms(Vec<Term>),
    Function(Vec<Term>),
    Underscore,
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
            Term::Underscore => write!(f, "_"),
        }
    }
}

/// Use to translate the `cong` rule
impl From<Operator> for Term {
    fn from(op: Operator) -> Self {
        match op {
            Operator::Not => Term::Alethe(LTerm::Neg(None)),
            Operator::Equals => Term::TermId("(⟺ᶜ)".to_string()),
            Operator::Or => Term::TermId("∨ᶜ".to_string()),
            Operator::And => Term::TermId("∧ᶜ".to_string()),
            Operator::LessEq => Term::TermId("≤".to_string()),
            Operator::LessThan => Term::TermId("<".to_string()),
            Operator::Implies => Term::TermId("⟹ᶜ".to_string()),
            o => todo!("Operator {:?}", o),
        }
    }
}

impl<S: Into<String>> From<S> for Term {
    fn from(id: S) -> Self {
        Term::TermId(id.into())
    }
}

impl From<&Rc<AletheTerm>> for Term {
    fn from(term: &Rc<AletheTerm>) -> Self {
        match &**term {
            AletheTerm::Sort(sort) => match sort {
                Sort::Function(params) => Term::Function(params.iter().map(Term::from).collect()),
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
                let mut args = args.into_iter().map(Term::from).collect::<VecDeque<_>>();
                return match operator {
                    Operator::Not => Term::Alethe(LTerm::Neg(Some(Box::new(
                        args.front().map(|a| Term::from(a.clone())).unwrap(),
                    )))),
                    Operator::Or => {
                        args.push_back(Term::Alethe(LTerm::False));
                        Term::Alethe(LTerm::NOr(args.into()))
                    }
                    Operator::Equals => Term::Alethe(LTerm::Eq(
                        Box::new(args[0].clone()),
                        Box::new(args[1].clone()),
                    )),
                    Operator::And => {
                        args.push_back(Term::Alethe(LTerm::True));
                        Term::Alethe(LTerm::NAnd(args.into()))
                    }
                    Operator::Implies => Term::Alethe(LTerm::Implies(
                        Box::new(args[0].clone()),
                        Box::new(args[1].clone()),
                    )),
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
            AletheTerm::Var(Ident::Simple(ident), _term) if ident == "true" => {
                Term::Alethe(LTerm::True)
            }
            AletheTerm::Var(Ident::Simple(ident), _term) if ident == "false" => {
                Term::Alethe(LTerm::False)
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
pub struct Param(String, Term);

impl fmt::Display for Param {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Param(id, _term) => write!(f, "{}", id),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Proof(pub Vec<ProofStep>);

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
pub enum ProofStep {
    Assume(Vec<String>),
    Apply(Term, Vec<Term>, SubProofs),
    Refine(Term, Vec<Term>, SubProofs),
    Have(String, Term, Vec<ProofStep>), //TODO: change Vec<ProofStep> for Proof
    Admit,
    Reflexivity,
}

#[derive(Debug, Clone)]
pub struct SubProofs(Option<Vec<Proof>>);

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
                        .join(WHITE_SPACE)
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
                            .join(WHITE_SPACE)
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
                        .join(WHITE_SPACE),
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
            (
                Command::Symbol(None, id.to_string(), vec![], TYPE(), None),
                Command::Rule(
                    Term::TermId(id.to_string()),
                    Term::TermId("τ o".to_string()), //FIXME: make a more concrete data type for `τ o`
                ),
            )
        })
        .flat_map(|tup| [tup.0, tup.1].into_iter())
        .collect::<Vec<Command>>();

    let mut function_declarations_symbols = prelude
        .function_declarations
        .into_iter()
        .map(|(id, term)| Command::Symbol(None, id.to_string(), vec![], Term::from(term), None))
        .collect::<Vec<Command>>();

    sort_declarations_symbols.append(&mut function_declarations_symbols);

    sort_declarations_symbols
}

pub fn produce_lambdapi_proof(
    proof_obligation_name: Option<String>,
    prelude: ProblemPrelude,
    proof_elaborated: ProofElaborated,
    named_map: IndexMap<String, FunctionDef>,
) -> TradResult<LambdapiFile> {
    let mut lambdapi_file = LambdapiFile::default();

    let prelude = translate_prelude(prelude);

    lambdapi_file.extend(prelude);

    let id_last_step = get_id_of_last_step(proof_elaborated.commands.as_slice());

    let mut context = Context::from(named_map);

    let proof_obligation_symbol = translate_commands(&mut context, &mut proof_elaborated.iter())
        .map(|mut proof| {
            // add the last apply to conclude the proof obligation
            proof.push(ProofStep::Apply(
                Term::TermId(id_last_step.to_string()),
                vec![],
                SubProofs(None),
            ));

            // Construct the symbol (Theorem) of the proof obligation
            // and inject the proof translated inside
            Command::Symbol(
                Some(Modifier::Opaque),
                proof_obligation_name.unwrap_or("proof_obligation".to_string()),
                vec![],
                Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(
                    Vec::new(),
                ))))),
                Some(Proof(proof)),
            )
        })?;

    add_dagify_subexpression_as_symbol(&context, &mut lambdapi_file);

    lambdapi_file.extend(context.prelude);

    lambdapi_file.push_back(proof_obligation_symbol);

    Ok(lambdapi_file)
}

#[inline]
fn add_dagify_subexpression_as_symbol(ctx: &Context, file: &mut LambdapiFile) {
    ctx.sharing_map.iter().for_each(|(term, (id, _))| {
        file.push_back(Command::Definition(id.into(), Term::from(term)));
    })
}

fn get_id_of_last_step(cmds: &[ProofCommand]) -> String {
    match cmds.iter().last().unwrap() {
        ProofCommand::Step(AstProofStep { id, .. }) => id.to_string(),
        _ => unreachable!(),
    }
}

fn get_premises_clause<'a>(
    proof_iter: &'a ProofIter,
    premises: &'a [(usize, usize)],
) -> Vec<(String, &'a [Rc<AletheTerm>])> {
    premises
        .into_iter()
        .map(|p| proof_iter.get_premise(*p))
        .map(|c| (normalize_name(c.id()), c.clause()))
        .collect_vec()
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
    let mut duration = Duration::ZERO;

    if terms.len() > 2 {
        let position = terms
            .iter()
            .position(|e| polyeq(e, pivot, &mut duration))
            .ok_or(TranslatorError::PivotNotInClause)?;
        path = itertools::repeat_n(Direction::Right, position).collect::<Vec<Direction>>();

        if position != terms.len() - 1 {
            path.push(Direction::Left);
        }
    } else {
        if polyeq(pivot, terms.first().unwrap(), &mut duration) {
            path.push(Direction::Left);
        } else {
            path.push(Direction::Right);
        };
    }
    Ok(path)
}

/// Remove the pivot and its negation form in a clause.
fn remove_pivot_in_clause<'a>(
    (pivot, flag): &(Rc<AletheTerm>, bool),
    clause_left: &[Rc<AletheTerm>],
    clause_right: &[Rc<AletheTerm>],
) -> Vec<Rc<AletheTerm>> {
    let mut duration = Duration::ZERO;

    //FIXME: pivot should be or there is a bug
    if *flag {
        let mut filtered_clause_left = clause_left.into_iter().map(|t| t.clone()).collect_vec();
        let index = filtered_clause_left
            .iter()
            .position(|t| polyeq(pivot, t, &mut duration));

        if let Some(index) = index {
            filtered_clause_left.remove(index);
        }

        let mut filtered_clause_right = clause_right.into_iter().map(|t| t.clone()).collect_vec();
        let index = filtered_clause_right
            .iter()
            .position(|t| polyeq(&term_negated(pivot), t, &mut duration));
        if let Some(index) = index {
            filtered_clause_right.remove(index);
        }

        filtered_clause_left.append(&mut filtered_clause_right);
        filtered_clause_left
    } else {
        let mut filtered_clause_left = clause_left.into_iter().map(|t| t.clone()).collect_vec();
        let index = filtered_clause_left
            .iter()
            .position(|t| polyeq(&term_negated(pivot), t, &mut duration));

        if let Some(index) = index {
            filtered_clause_left.remove(index);
        }

        let mut filtered_clause_right = clause_right.into_iter().map(|t| t.clone()).collect_vec();
        let index = filtered_clause_right
            .iter()
            .position(|t| polyeq(&pivot, t, &mut duration));

        if let Some(index) = index {
            filtered_clause_right.remove(index);
        }

        filtered_clause_left.append(&mut filtered_clause_right);
        filtered_clause_left
    }
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
            hyp_right_arg = Term::Terms(vec![
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
    let mut duration = Duration::ZERO;
    terms.len() > 0 && polyeq(term, &terms[0], &mut duration)
}

/// Generate a sublemma to move the pivot. Consider the pivot `x` and the clause (cl a b (not x) c)
/// this function will create the sublemma step to move the pivot:
/// have move_head_notx: Prf((a ⟇ b ⟇ x ⟇ c)  →  (x ⟇ a ⟇ b ⟇ c))  {
///     [proof generated here]
/// }
fn move_pivot_lemma(name: &str, pivot: &Rc<AletheTerm>, clause: &[Rc<AletheTerm>]) -> ProofStep {
    let mut duration = Duration::ZERO;
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
        .filter(|t| polyeq(pivot, t, &mut duration) == false)
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

#[inline]
/// Lambdapi does not support symbol name containing dot so
/// they are replace by underscore.
fn normalize_name<S: AsRef<str>>(name: S) -> String {
    // call as_ref() to get a &str
    name.as_ref().replace(".", "_")
}

/// Map some rule name to their corresponding symbol in the Lambdapi stdlib
fn translate_rule_name(rule: &str) -> Term {
    match rule {
        "refl" => Term::TermId("⟺ᶜ_refl".to_string()),
        "symm" => Term::TermId("⟺ᶜ_sym".to_string()),
        "trans" => Term::TermId("⟺ᶜ_trans".to_string()),
        r => Term::TermId(r.to_string()),
    }
}

/// Assume alethe add an axiom in the prelude of the proof obligation.
/// Axiom are opaque symbol.
fn translate_assume(ctx: &mut Context, id: &str, term: &Rc<AletheTerm>) {
    let axiom_symbol = Command::Symbol(
        Some(Modifier::Constant),
        id.to_string(),
        vec![],
        Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(vec![
            Term::from(term),
        ]))))),
        None,
    );
    ctx.prelude.push(axiom_symbol);
}

/// Translate (anchor :step ti) and its steps
/// A subproof is translated into an opaque symbol
/// added to the prelude of the file.
fn translate_subproof<'a>(
    context: &mut Context,
    iter: &mut ProofIter<'a>,
    commands: &[ProofCommand],
) -> TradResult<Vec<ProofStep>> {
    let subproof = commands.last().unwrap();

    let (id, clause) = unwrap_match!(
        subproof,
        ProofCommand::Step(AstProofStep { id, clause, .. }) => (normalize_name(id), clause)
    );

    let clause = clause.iter().map(From::from).collect_vec();

    let mut fresh_ctx = Context::default();
    fresh_ctx.sharing_map = context.sharing_map.clone();

    let mut proof = translate_commands(&mut fresh_ctx, iter)?;

    //TODO: Remove this side effect by append the prelude in translate_commands and return the  pair Subproof + Axioms in subproof
    context.prelude.append(&mut fresh_ctx.prelude); // Add subproof of current subproof to the prelude

    let psy_id = unwrap_match!(commands.get(commands.len() - 2), Some(ProofCommand::Step(AstProofStep{id, ..})) => normalize_name(id));

    let discharge = unwrap_match!(commands.last(), Some(ProofCommand::Step(AstProofStep{id: _, clause:_, rule:_, premises:_, args:_, discharge})) => discharge);

    let premises_discharge = get_premises_clause(iter, discharge);

    let subproof_tactic = Term::TermId(format!("subproof{}", premises_discharge.len()));

    let mut args = premises_discharge
        .into_iter()
        .map(|(id, _)| Term::TermId(id))
        .collect_vec();
    args.push(Term::TermId(psy_id.to_string()));

    proof.push(ProofStep::Apply(subproof_tactic, args, SubProofs(None)));

    let subproof_have = vec![ProofStep::Have(
        id.to_string(),
        Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(clause))))),
        proof,
    )];

    Ok(subproof_have)
}

/// Create a proof step for the resolution
fn translate_resolution(
    _ctx: &Context,
    proof_iter: &mut ProofIter<'_>,
    id: &str,
    clause: &[Rc<AletheTerm>],
    premises: &[(usize, usize)],
    args: &[ProofArg],
) -> TradResult<ProofStep> {
    let premises = get_premises_clause(&proof_iter, premises);

    let pivots = get_pivots_from_args(args);

    let (last_goal_name, _, mut steps) = match premises.as_slice() {
        [h1, h2, tl_premises @ ..] => match pivots.as_slice() {
            [pivot, tl_pivot @ ..] => tl_premises.into_iter().zip(tl_pivot.into_iter()).fold(
                (
                    format!("{}_{}", h1.0, h2.0),
                    remove_pivot_in_clause(&pivot, h1.1, h2.1),
                    vec![ProofStep::Have(
                        format!("{}_{}", h1.0, h2.0),
                        proof(Term::Alethe(LTerm::Clauses(
                            remove_pivot_in_clause(&pivot, h1.1, h2.1)
                                .into_iter()
                                .map(|s| Term::from(s))
                                .collect::<Vec<Term>>(),
                        ))),
                        make_resolution(pivot, &(&h1.0, h1.1), &(&h2.0, h2.1)),
                    )],
                ),
                |(previous_goal_name, previous_goal, mut proof_steps), (premise, pivot)| {
                    let goal_name = format!("{}_{}", previous_goal_name, premise.0);

                    let current_goal =
                        remove_pivot_in_clause(&pivot, previous_goal.as_slice(), premise.1);

                    let resolution = make_resolution(
                        pivot,
                        &(format!("{}", previous_goal_name).as_str(), &previous_goal),
                        &(&premise.0, premise.1),
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
            ),
            _ => unreachable!(),
        },
        _ => unreachable!(),
    };

    steps.push(ProofStep::Refine(
        Term::TermId(last_goal_name),
        vec![],
        SubProofs(None),
    ));

    Ok(ProofStep::Have(
        id.to_string(),
        proof(Term::Alethe(LTerm::Clauses(
            clause.iter().map(|s| Term::from(s)).collect::<Vec<Term>>(),
        ))),
        steps,
    ))
}

/// Create a proof step for tautology step (equiv_pos1, and_neg, etc)
fn translate_tautology(
    ctx: &Context,
    proof_iter: &mut ProofIter<'_>,
    id: &str,
    clause: &[Rc<AletheTerm>],
    premises: &[(usize, usize)],
    rule: &str,
) -> Option<TradResult<ProofStep>> {
    let premises: Vec<_> = get_premises_clause(&proof_iter, &premises);

    let clauses = clause
        .into_iter()
        .map(|term| ctx.get_or_convert(term))
        .collect();

    let steps = match rule {
        "bind" | "subproof" => None,
        "reordering" | "contraction" => Some(Ok(Proof(vec![ProofStep::Admit]))),
        "cong" => Some(translate_cong(clause, premises.as_slice())),
        "and_neg" | "or_neg" | "and_pos" => Some(translate_auto_rewrite(rule)),
        "not_or" => Some(translate_not_or(
            premises.first().unwrap().0.as_str(),
            premises.first().unwrap().1.as_ref(),
        )),
        "implies" => Some(translate_implies(premises.first().unwrap().0.as_str())),
        "trans" => Some(translate_trans(premises.as_slice())),
        "symm" => Some(translate_sym(premises.first().unwrap().0.as_str())),
        "refl" => Some(translate_refl()),
        "or" => Some(translate_or(premises.first().unwrap().0.as_str())),
        _ => Some(translate_simple_tautology(rule, premises.as_slice())),
    };

    steps.map(|steps| {
        Ok(ProofStep::Have(
            id.to_string(),
            proof(Term::Alethe(LTerm::Clauses(clauses))),
            steps?.0,
        ))
    })
}

fn translate_trans(premises: &[(String, &[Rc<AletheTerm>])]) -> TradResult<Proof> {
    Ok(Proof(vec![ProofStep::Apply(
        Term::from("⟇ᵢ₁'"),
        vec![Term::Terms(vec![
            Term::from("⟺ᶜ_trans"),
            unary_cl_in_prf(premises.get(0).unwrap().0.as_str()),
            unary_cl_in_prf(premises.get(1).unwrap().0.as_str()),
        ])],
        SubProofs(None),
    )]))
}

fn translate_implies(premise: &str) -> TradResult<Proof> {
    Ok(Proof(vec![ProofStep::Apply(
        Term::from("implies"),
        vec![unary_cl_in_prf(premise)],
        SubProofs(None),
    )]))
}

fn translate_refl() -> TradResult<Proof> {
    Ok(Proof(vec![
        ProofStep::Apply(Term::from("π_to_π̇"), vec![], SubProofs(None)),
        ProofStep::Apply(Term::from("∨ᶜᵢ₁"), vec![], SubProofs(None)),
        ProofStep::Apply(Term::from("⟺ᶜ_refl"), vec![], SubProofs(None)),
    ]))
}

fn translate_sym(premise: &str) -> TradResult<Proof> {
    Ok(Proof(vec![
        ProofStep::Apply(Term::from("π_to_π̇"), vec![], SubProofs(None)),
        ProofStep::Apply(Term::from("∨ᶜᵢ₁"), vec![], SubProofs(None)),
        ProofStep::Apply(
            Term::from("⟺ᶜ_sym"),
            vec![unary_cl_in_prf(premise)],
            SubProofs(None),
        ),
    ]))
}

/// Corresponding to the symbol application π̇ₗ x,
/// where π̇ₗ: π̇ (a ⟇ □)  → π a
fn unary_cl_in_prf(premise_id: &str) -> Term {
    Term::Terms(vec![Term::from("π̇ₗ"), Term::from(premise_id)])
}

#[inline]
fn translate_not_or(premise_id: &str, premise_clause: &[Rc<AletheTerm>]) -> TradResult<Proof> {
    let apply_identity = Proof(vec![ProofStep::Apply(
        Term::TermId("identity_⊥".into()),
        vec![Term::Terms(vec![
            Term::TermId("π̇_to_π".to_string()),
            Term::TermId(premise_id.into()),
        ])],
        SubProofs(None),
    )]);
    let reflexivity = Proof(vec![ProofStep::Reflexivity]);

    let disjunctions = unwrap_match!(premise_clause.first().unwrap().deref(), AletheTerm::Op(Operator::Not, args) => args)
        .into_iter()
        .map(From::from)
        .collect_vec();

    Ok(Proof(vec![ProofStep::Apply(
        Term::TermId("not_or".into()),
        vec![Term::Terms(disjunctions)],
        SubProofs(Some(vec![apply_identity, reflexivity])),
    )]))
}

#[inline]
fn translate_or(premise_id: &str) -> TradResult<Proof> {
    Ok(Proof(vec![ProofStep::Apply(
        Term::TermId("or".into()),
        vec![Term::TermId(premise_id.into())],
        SubProofs(None),
    )]))
}

#[inline]
fn translate_auto_rewrite(rule: &str) -> TradResult<Proof> {
    Ok(Proof(vec![
        ProofStep::Apply(Term::TermId(rule.into()), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]))
}

fn translate_cong(
    clause: &[Rc<AletheTerm>],
    premises: &[(String, &[Rc<AletheTerm>])],
) -> TradResult<Proof> {
    let operator = unwrap_match!(clause[0].deref(), AletheTerm::Op(Operator::Equals, ts) => {
        match (&*ts[0], &*ts[1]) {
            (AletheTerm::App(f, ..) , AletheTerm::App(g, _)) if f == g => Term::from((*f).clone()),
            (AletheTerm::Op(f, ..) , AletheTerm::Op(g, _)) if f == g => Term::from(*f),
            _ => unreachable!()
        }
    });

    let mut premises_rev = premises
        .into_iter()
        .map(|(name, _)| name.clone())
        .collect::<VecDeque<String>>();

    let first = premises_rev.pop_back().expect("cong without first premise");
    let second = premises_rev
        .pop_back()
        .expect("cong without second premise");

    let first_cong = Term::Terms(vec![
        Term::from("cong2"),
        operator.clone(),
        Term::from(second),
        Term::from(first),
    ]);

    let cong = premises_rev.into_iter().fold(first_cong, |acc, ti| {
        Term::Terms(vec![
            Term::from("cong2"),
            operator.clone(),
            Term::from(ti),
            acc,
        ])
    });

    Ok(Proof(vec![ProofStep::Apply(cong, vec![], SubProofs(None))]))
}

fn translate_simple_tautology(
    rule: &str,
    premises: &[(String, &[Rc<AletheTerm>])],
) -> TradResult<Proof> {
    Ok(Proof(vec![ProofStep::Apply(
        translate_rule_name(rule),
        premises
            .into_iter()
            .map(|(name, _)| Term::TermId(name.to_string()))
            .collect_vec(),
        SubProofs(None),
    )]))
}

/// Create a proof step for tautology step.
/// TODO: This feature need the RARE rewriting system to be implemented.
fn translate_simplification(
    _ctx: &Context,
    id: &str,
    clause: &[Rc<AletheTerm>],
    _rule: &str,
) -> TradResult<ProofStep> {
    let terms = clause.into_iter().map(|a| Term::from(a)).collect();

    Ok(ProofStep::Have(
        id.to_string(),
        proof(Term::Alethe(LTerm::Clauses(terms))),
        vec![ProofStep::Admit],
    ))
}

fn translate_commands<'a>(
    ctx: &mut Context,
    proof_iter: &mut ProofIter<'a>,
) -> TradResult<Vec<ProofStep>> {
    let mut proof_steps = Vec::new();

    while let Some(command) = proof_iter.next() {
        match command {
            ProofCommand::Assume { id, term } => {
                translate_assume(ctx, normalize_name(id).as_str(), term)
            }
            ProofCommand::Step(AstProofStep {
                id,
                clause,
                premises,
                rule,
                args,
                discharge: _,
            }) if rule == "resolution" || rule == "th_resolution" => {
                let proof = translate_resolution(
                    &ctx,
                    proof_iter,
                    id.replace(".", "_").as_str(),
                    clause,
                    premises,
                    args,
                )?;
                proof_steps.push(proof);
            }
            ProofCommand::Step(AstProofStep { id, clause, premises: _, rule, .. })
                if rule.contains("simp") =>
            {
                let step =
                    translate_simplification(&ctx, normalize_name(id).as_str(), clause, rule)?;
                proof_steps.push(step);
            }
            ProofCommand::Step(AstProofStep { id, clause, premises, rule, .. }) => {
                let step = translate_tautology(
                    &ctx,
                    proof_iter,
                    normalize_name(id).as_str(),
                    clause,
                    premises,
                    rule,
                );

                if let Some(step) = step {
                    proof_steps.push(step?);
                }

                // Iteration is flatten with the ProofIter, so we need to break the looping if we
                // are in a subproof because the Subproof case use a recursive call.
                if proof_iter.is_end_step() {
                    break;
                }
            }
            ProofCommand::Subproof(Subproof { commands, .. }) => {
                let mut subproof = translate_subproof(ctx, proof_iter, commands.as_slice())?;
                proof_steps.append(&mut subproof);
            }
        };
    }

    Ok(proof_steps)
}

#[derive(Default)]
pub struct Context {
    prelude: Vec<Command>,
    /// Sharing map contains all the dagify common sub expression generated by the SMT-solver
    /// with the `:named` annotation. This feature make step more compact and easier to debug.
    /// We do not propose an option to disable this feature because it is enough to run Carcara translation
    /// by providing a proof file without `:named` annotation.
    sharing_map: IndexMap<Rc<AletheTerm>, (String, Vec<(String, Rc<AletheTerm>)>)>, //FIXME: Add an R
}

impl<'a> From<IndexMap<String, FunctionDef>> for Context {
    fn from(map: IndexMap<String, FunctionDef>) -> Self {
        let mut named_map = IndexMap::new();

        // We filter all the :named in assert to keep only
        // the common sub expressions for terms and the Goal
        map.into_iter()
            .filter(|(k, _)| k.contains("@") || k == "Goal")
            .for_each(|(k, v)| {
                named_map.insert(v.body, (k.replace("@", ""), v.params));
            });

        Self {
            prelude: Vec::new(),
            sharing_map: named_map,
        }
    }
}

impl Context {
    /// Convert dagify subexpression into `Term::TermId` otherwise just apply a canonical conversion
    fn get_or_convert(&self, term: &Rc<AletheTerm>) -> Term {
        if let Some((shared_id, _sort)) = self.sharing_map.get(term) {
            Term::TermId(shared_id.to_string())
        } else {
            Term::from(term)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{ast::ProofCommand, checker, checker::Config, parser};
    use std::io::Cursor;

    use super::get_pivots_from_args;
    #[test]
    #[ignore]
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

        let (prelude, proof, mut pool, _) = parser::parse_instance(
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
    #[ignore]
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

        let (prelude, proof, mut pool, _) = parser::parse_instance(
            Cursor::new(definitions),
            Cursor::new(proof),
            parser::Config::default(),
        )
        .expect("parse proof and definition");

        let mut checker = checker::ProofChecker::new(&mut pool, Config::new(), &prelude);
        let (_, elaborated) = checker.check_and_elaborate(proof).unwrap();

        //let res = super::translate_proof_step(elaborated);

        //println!("{}", res);
    }
}
