use crate::ast::AnchorArg;
#[allow(const_item_mutation)]
use crate::ast::{
    polyeq, Operator, ProblemPrelude, Proof as ProofElaborated, ProofCommand, ProofIter,
    ProofStep as AstProofStep, Rc, Sort, Subproof, Term as AletheTerm,
};
use crate::parser::FunctionDef;
use indexmap::IndexMap;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{self};
use std::time::Duration;
use try_match::unwrap_match;

use itertools::Itertools;
use thiserror::Error;

pub mod output;
pub mod printer;
pub mod proof;
mod simp;
mod tautology;
pub mod term;

use output::*;
use proof::*;
use simp::*;
use tautology::*;
use term::*;

#[derive(Debug, Error)]
pub enum TranslatorError {
    #[error("the pivot is not in the clause")]
    PivotNotInClause,
    #[error("the premises are incorrect")]
    PremisesError,
}

pub type TradResult<T> = Result<T, TranslatorError>;

#[derive(Default)]
pub struct Context {
    prelude: Vec<Command>,
    /// Sharing map contains all the dagify common sub expression generated by the SMT-solver
    /// with the `:named` annotation. This feature make step more compact and easier to debug.
    /// We do not propose an option to disable this feature because it is enough to run Carcara translation
    /// by providing a proof file without `:named` annotation.
    sharing_map: IndexMap<Rc<AletheTerm>, (String, Vec<(String, Rc<AletheTerm>)>)>, //FIXME: Add an R
    /// Dependencies of premises as a map Index ↦ location, depth, [Index] where Index represent
    /// the location of the premise in the proof.
    deps: HashMap<String, (usize, usize, HashSet<usize>)>,
    index: usize,
}

impl<'a> From<IndexMap<String, FunctionDef>> for Context {
    fn from(map: IndexMap<String, FunctionDef>) -> Self {
        let mut named_map = IndexMap::new();

        // We filter all the :named in assert to keep only
        // the common sub expressions for terms
        map.into_iter()
            .filter(|(k, _)| k.contains("@"))
            .for_each(|(k, v)| {
                named_map.insert(v.body, (k.replace("@", ""), v.params));
            });

        Self {
            prelude: Vec::new(),
            sharing_map: named_map,
            deps: HashMap::new(),
            index: 0,
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

#[inline]
fn set() -> Term {
    Term::TermId("Set".into())
}

#[inline]
fn omicron() -> Term {
    Term::TermId("o".into())
}

#[inline]
fn index() -> Term {
    Term::TermId("𝑰".into())
}

#[inline]
fn tau(term: Term) -> Term {
    //TODO: Print without parenthesis when there is only 1 sort
    Term::TermId(format!("τ ({})", term))
}

#[inline]
fn proof(term: Term) -> Term {
    Term::Alethe(LTerm::Proof(Box::new(term)))
}

/// Corresponding to the symbol application π̇ₗ x,
/// where π̇ₗ: π̇ (a ⟇ □)  → π a
pub fn unary_clause_to_prf(premise_id: &str) -> Term {
    Term::Terms(vec![Term::from("π̇ₗ"), Term::from(premise_id)])
}

macro_rules! make_term {
    ( ($( $args:tt ) +) ) => { make_term![  $( $args) + ] };
    (_) => { Term::Underscore };
    (or $i:ident) => { Term::Alethe(LTerm::NOr($i)) };
    (and $i:ident) => { Term::Alethe(LTerm::NAnd($i)) };
    ($l:tt => $r:tt) => { Term::Alethe(LTerm::Implies(Box::new(make_term![$l]) ,  Box::new(make_term![$r]))) };
    ( $f:tt ( $( $args:tt ) + ) ) => { Term::Terms(vec![  make_term![$f], $( make_term![$args] ) , + ]) };
    ( @$( $exp:tt )+ ) => { $( $exp )+  };
    ($f:tt) => { Term::from($f) };
}

pub(crate) use make_term;

macro_rules! inline_lambdapi {
    ($($tokens:tt)+) => {
        {
            lambdapi_wrapper!(
                begin
                    $($tokens)+
                end;
            ).pop().unwrap()
        }
    }
}

pub(crate) use inline_lambdapi;

macro_rules! tactic {
    ($steps:ident, symmetry; $($body:tt)*) => { $steps.push(ProofStep::Symmetry) ; tactic![ $steps, $( $body )* ] };
    ($steps:ident, reflexivity; $($body:tt)*) => { $steps.push(ProofStep::Reflexivity) ; tactic![ $steps, $( $body )* ] };
    ($steps:ident, apply $i:tt; $($body:tt)+) => {
        $steps.push(ProofStep::Apply(Term::from($i), vec![], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, apply @$e:expr; $($body:tt)+) => {
        $steps.push(ProofStep::Apply(make_term![$e], vec![], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, apply $i:tt $arg:tt; $($body:tt)+) => {
        $steps.push(ProofStep::Apply(Term::from($i), vec![ make_term![$arg] ], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, apply $i:tt  $( ( $($args:tt) + ) ) * ; $($body:tt)+) => {
        $steps.push(ProofStep::Apply(Term::from($i), vec![ $( make_term![  $( $args )+ ] , )* ], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, apply $i:tt  $( ( $($args:tt) + ) ) * $( { $($subproof:tt) + } ) + ; $($body:tt)+) => {
        let mut sub_proofs: Vec<Proof> = Vec::new();

        $(
            {
                let sub_proof = lambdapi_wrapper!{ begin $( $subproof )+ end; };
                sub_proofs.push(Proof(sub_proof));
            }
        )*;

        $steps.push(ProofStep::Apply(Term::from($i), vec![ $( make_term![  $( $args )+ ] , )* ], SubProofs(Some(sub_proofs))));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, have $i:tt : ( $($goal:tt) + ) {  $( $body_have:tt )+  }  ; $($body:tt)*) => {
        let have_body: Vec<ProofStep> = lambdapi!{ $( $body_have )+ };
        $steps.push(ProofStep::Have(stringify!($i).to_string(), make_term![  $( $goal )+ ] ,have_body))  ; tactic![ $steps, $( $body )* ]
    };
    ($steps:ident, assume [$($id:tt)+] ; $($body:tt)*) => {
        let mut ids: Vec<String> = Vec::new();

        $(
            ids.push(stringify!($id).to_string());
        )+

        $steps.push(ProofStep::Assume(ids));
        tactic![ $steps, $(  $body )* ]
    };
    ($steps:ident, try [ $($id:tt)+ ] ; $($body:tt)*) => {
        let step = inline_lambdapi![ $( $id )+ ];

        $steps.push(ProofStep::Try(Box::new(step)));
        tactic![ $steps, $(  $body )* ]
    };
    ($steps:ident, rewrite [$($i:tt)+] $( ( $($args:tt) + ) ) * ; $($body:tt)+) => {
        $steps.push(ProofStep::Rewrite(None, $($i)+, vec![ $( make_term![  $( $args )+ ] , )* ]));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, rewrite .$pattern:tt $i:tt  $( ( $($args:tt) + ) ) * ; $($body:tt)+) => {
        $steps.push(ProofStep::Rewrite(Some($pattern.to_string()), Term::from($i), vec![ $( make_term![  $( $args )+ ] , )* ]));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, rewrite $i:tt  $( ( $($args:tt) + ) ) * ; $($body:tt)+) => {
        $steps.push(ProofStep::Rewrite(None, Term::from($i), vec![ $( make_term![  $( $args )+ ] , )* ]));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, $code:block ; $($body:tt)*) => {  $steps.append(&mut $code) ; tactic![ $steps, $(  $body )* ]  };
    ($steps:ident, inject($code:expr) ; $($body:tt)*) => {  $steps.append(&mut $code) ; tactic![ $steps, $(  $body )* ]  };
    ($steps:ident, admit; $($body:tt)*) => { $steps.push(ProofStep::Admit)  ; tactic![ $steps, $(  $body )* ]  };
    ($steps:ident, end;) => { };
}

pub(crate) use tactic;

macro_rules! lambdapi_wrapper {
    (begin $($body:tt)+) => { { let mut steps: Vec<ProofStep> = vec![];  tactic![ steps, $( $body )+ ] ; steps } };
}

pub(crate) use lambdapi_wrapper;

macro_rules! lambdapi {
    ($($body:tt)+) => { { lambdapi_wrapper!{ begin $($body)+ end; } } };
}

pub(crate) use lambdapi;

fn translate_sort_function(sort: &Sort) -> Term {
    match sort {
        Sort::Bool => omicron(),
        Sort::Int => "int".into(),
        Sort::Function(params) => {
            let sorts = params
                .into_iter()
                .map(|t| unwrap_match!(**t, AletheTerm::Sort(ref s) => s))
                .map(|s| translate_sort_function(s))
                .collect_vec();

            sorts
                .into_iter()
                .reduce(|acc, e| Term::Sort(BuiltinSort::Arrow(Box::new(acc), Box::new(e))))
                .unwrap()
        }
        Sort::Atom(ref a, args) => {
            if args.is_empty() {
                a.into()
            } else {
                let mut args: Vec<Term> = args.into_iter().map(Into::into).collect_vec();
                let mut sort = vec![a.into()];
                sort.append(&mut args);
                Term::Terms(sort)
            }
        }
        ref e => unreachable!("{:?}", e),
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
        .into_iter()
        .map(|(id, arity)| {
            let sorts = itertools::repeat_n(set(), arity + 1).collect_vec();
            Command::Definition(id.to_string(), vec![], Some(Term::Function(sorts)), None)
        })
        .collect::<Vec<Command>>();

    let mut function_declarations_symbols = prelude
        .function_declarations
        .into_iter()
        .enumerate()
        .map(|(counter, (id, term))| {
            let sort = match *term {
                AletheTerm::Sort(ref s) => tau(translate_sort_function(s)),
                _ => unreachable!(),
            };
            let index = Term::Terms(vec![index(), Term::TermId(format!("{}", counter))]);

            Command::Definition(id.to_string(), vec![], Some(sort), Some(index))
        })
        .collect::<Vec<Command>>();

    sort_declarations_symbols.append(&mut function_declarations_symbols);

    sort_declarations_symbols
}

#[inline]
fn gen_required_module() -> Vec<Command> {
    vec![
        Command::RequireOpen("Stdlib.Prop".to_string()),
        Command::RequireOpen("Stdlib.Set".to_string()),
        Command::RequireOpen("Stdlib.Eq".to_string()),
        Command::RequireOpen("Stdlib.Nat".to_string()),
        //Command::RequireOpen("Stdlib.Z".to_string()), //FIXME: Intersection between builtin Nat and Z
        Command::RequireOpen("lambdapi.Classic".to_string()),
        Command::RequireOpen("lambdapi.Alethe".to_string()),
        Command::RequireOpen("lambdapi.Simplify".to_string()),
        Command::RequireOpen("lambdapi.Rare".to_string()),
    ]
}

pub fn produce_lambdapi_proof<'a>(
    prelude: ProblemPrelude,
    proof_elaborated: ProofElaborated,
    named_map: IndexMap<String, FunctionDef>,
) -> TradResult<ProofFile> {
    let mut proof_file = ProofFile::new();

    proof_file.requires = gen_required_module();

    proof_file.definitions = translate_prelude(prelude);

    let mut context = Context::from(named_map);

    let commands = translate_commands(
        &mut context,
        &mut proof_elaborated.iter(),
        0,
        |id, t, ps| Command::Symbol(None, normalize_name(id), vec![], t, Some(Proof(ps))),
    )?;

    add_dagify_subexpression_as_symbol(&context, &mut proof_file);

    proof_file.content.extend(commands);

    proof_file.dependencies = context
        .deps
        .into_iter()
        .map(|(k, (loc, _depth, deps))| (k, (loc, deps)))
        .collect::<HashMap<_, _>>();

    Ok(proof_file)
}

#[inline]
fn add_dagify_subexpression_as_symbol(ctx: &Context, file: &mut ProofFile) {
    ctx.sharing_map.iter().for_each(|(term, (id, _))| {
        file.content.push(Command::Definition(
            id.into(),
            vec![],
            Some(Term::from(term)),
            None,
        ));
    })
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

fn get_pivots_from_args(args:  &Vec<Rc<AletheTerm>>) -> Vec<(Rc<AletheTerm>, bool)> {
    args.into_iter()
        .tuples()
        .map(|(x, y)| match (x, y) {
            (pivot, flag) if flag.is_bool_true() => {
                ((*pivot).clone(), true)
            }
            (pivot, flag) if flag.is_bool_false() => {
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
    Rc::new(AletheTerm::Op(Operator::Not, vec![term.clone()]))
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

    let proof_script = gen_move_pivot_proof(clause, new_clause2.as_slices().0).0;

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

fn gen_move_pivot_proof(clauses: &[Rc<AletheTerm>], new_clauses: &[Rc<AletheTerm>]) -> Proof {
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
                    gen_move_pivot_proof(&clauses[1..clauses.len()], new_clauses),
                ])),
            ),
        ])
    }
}

#[inline]
/// Lambdapi does not support symbol name containing dot so
/// they are replace by underscore.
/// SMTLIB quoted symbols `|x|` allow to have pretty much any character in a symbol.
/// However that is incompatible with identifier of Lambdapi.
fn normalize_name<S: AsRef<str>>(name: S) -> String {
    // call as_ref() to get a &str
    name.as_ref()
        .replace(".", "_")
        .replace(printer::WHITE_SPACE, "")
        .replace("$", "")
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

/// Translate (anchor :step ti) and its steps
/// A subproof is translated into an opaque symbol
/// added to the prelude of the file.
fn translate_subproof<'a>(
    context: &mut Context,
    iter: &mut ProofIter<'a>,
    commands: &[ProofCommand],
    assignment_args: Vec<(&(String, Rc<AletheTerm>), &Rc<AletheTerm>)>,
    depth: usize,
) -> TradResult<(
    String,
    Vec<Term>,
    Vec<ProofStep>,
    HashMap<String, (usize, usize, HashSet<usize>)>,
)> {
    let subproof = commands.last().unwrap();

    //Get the last step of the proof
    let (id, clause, rule) = unwrap_match!(
        subproof,
        ProofCommand::Step(AstProofStep { id, clause, rule,.. }) => (normalize_name(id), clause, rule)
    );

    let clause = clause.iter().map(From::from).collect_vec();

    let mut fresh_ctx = Context::default();
    fresh_ctx.sharing_map = context.sharing_map.clone();
    fresh_ctx.deps = context.deps.clone();

    let mut proof_cmds = translate_commands(&mut fresh_ctx, iter, depth + 1, |id, t, ps| {
        ProofStep::Have(normalize_name(id), t, ps)
    })?;

    proof_cmds
        .iter_mut()
        .filter(|cmd| matches!(cmd, ProofStep::Have(_, _, _)))
        .for_each(|cmd| match cmd {
            ProofStep::Have(name, cl, steps) => {
                cl.visit(&assignment_args);
                *cmd = ProofStep::Have(name.to_string(), cl.clone(), steps.to_vec());
            }
            _ => {}
        });

    let assignment_args = assignment_args
        .into_iter()
        .map(|(_, term)| Term::from(term))
        .collect_vec();

    //TODO: Remove this side effect by append the prelude in translate_commands and return the  pair Subproof + Axioms in subproof
    context.prelude.append(&mut fresh_ctx.prelude); // Add subproof of current subproof to the prelude

    let subproof_have_wrapper = if rule == "bind" {
        let mut proof = vec![];

        let last_step_id = unwrap_match!(commands.get(commands.len() - 2), Some(ProofCommand::Step(AstProofStep{id, ..})) => normalize_name(id));

        let bind_lemma = match clause.first() {
            Some(Term::Alethe(LTerm::Eq(l, r)))
                if matches!(**l, Term::Alethe(LTerm::Forall(_, _)))
                    && matches!(**r, Term::Alethe(LTerm::Forall(_, _))) =>
            {
                "bind_∀"
            }
            Some(Term::Alethe(LTerm::Eq(l, r)))
                if matches!(**l, Term::Alethe(LTerm::Exist(_, _)))
                    && matches!(**r, Term::Alethe(LTerm::Exist(_, _))) =>
            {
                "bind_∃"
            }
            _ => unreachable!(),
        };

        proof.push(ProofStep::Apply(
            Term::from("∨ᶜᵢ₁"),
            vec![],
            SubProofs(None),
        ));
        assignment_args.into_iter().for_each(|term| {
            proof.push(ProofStep::Apply(
                Term::from(bind_lemma),
                vec![],
                SubProofs(None),
            ));
            proof.push(ProofStep::Assume(vec![format!("{}", term)]));
        });
        proof.append(&mut proof_cmds);

        proof.push(ProofStep::Apply(
            Term::from("π̇ₗ"),
            vec![Term::from(last_step_id)],
            SubProofs(None),
        ));

        proof
    } else if rule == "sko_forall" {
        let last_step_id = unwrap_match!(commands.get(commands.len() - 1), Some(ProofCommand::Step(AstProofStep{id, ..})) => normalize_name(id));

        // end of the script
        proof_cmds.append(&mut lambdapi! {
            apply "∨ᶜᵢ₁";
            apply "π̇ₗ" (@last_step_id.into());
        });

        proof_cmds
    } else {
        let psy_id = unwrap_match!(commands.get(commands.len() - 2), Some(ProofCommand::Step(AstProofStep{id, ..})) => normalize_name(id));

        let discharge = unwrap_match!(commands.last(), Some(ProofCommand::Step(AstProofStep{id: _, clause:_, rule:_, premises:_, args:_, discharge})) => discharge);

        let premises_discharge = get_premises_clause(iter, discharge);

        let subproof_tactic = Term::TermId(format!("subproof{}", premises_discharge.len()));

        let mut args = premises_discharge
            .into_iter()
            .map(|(id, _)| unary_clause_to_prf(id.as_str()))
            .collect_vec();
        args.push(unary_clause_to_prf(psy_id.as_str()));

        proof_cmds.push(ProofStep::Apply(subproof_tactic, args, SubProofs(None)));

        proof_cmds
    };

    Ok((id, clause, subproof_have_wrapper, fresh_ctx.deps))
}

/// Create a proof step for the resolution
fn translate_resolution(
    proof_iter: &mut ProofIter<'_>,
    premises: &[(usize, usize)],
    args: &Vec<Rc<AletheTerm>>,
) -> TradResult<Vec<ProofStep>> {
    
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

    Ok(steps)
}

// Create a proof step for tautology step (equiv_pos1, and_neg, etc)
fn translate_tautology(
    proof_iter: &mut ProofIter<'_>,
    clause: &[Rc<AletheTerm>],
    premises: &[(usize, usize)],
    rule: &str,
    args: &Vec<Rc<AletheTerm>>,
) -> Option<TradResult<Proof>> {
    let premises: Vec<_> = get_premises_clause(&proof_iter, &premises);

    match rule {
        "bind" | "subproof" => None,
        "false" => Some(translate_false()),
        "forall_inst" => Some(translate_forall_inst(args)),
        "cong" => Some(translate_cong(clause, premises.as_slice())),
        "and_neg" | "or_neg" | "and_pos" | "or_pos" => Some(translate_auto_rewrite(rule)),
        "not_or" => Some(translate_not_or(premises.first()?)),
        "implies" => Some(translate_implies(premises.first()?.0.as_str())),
        "not_implies1" => Some(translate_not_implies1(premises.first()?.0.as_str())),
        "not_implies2" => Some(translate_not_implies2(premises.first()?.0.as_str())),
        "not_and" => Some(translate_not_and(premises.first()?.0.as_str())),
        "not_symm" => Some(translate_not_symm(premises.first()?.0.as_str())),
        "trans" => Some(translate_trans(premises.as_slice())),
        "symm" => Some(translate_sym(premises.first()?.0.as_str())),
        "refl" => Some(translate_refl()),
        "and" => Some(translate_and(premises.first()?)),
        "or" => Some(translate_or(premises.first()?.0.as_str())),
        "sko_forall" => Some(translate_sko_forall()),
        "hole" | "reordering" | "contraction" => Some(Ok(Proof(vec![ProofStep::Admit]))), // specific rules of CVC5
        _ => Some(translate_simple_tautology(rule, premises.as_slice())),
    }
}

fn translate_commands<'a, F, T>(
    ctx: &mut Context,
    proof_iter: &mut ProofIter<'a>,
    depth: usize,
    f: F,
) -> TradResult<Vec<T>>
where
    F: Fn(String, Term, Vec<ProofStep>) -> T,
{
    let mut proof_steps = Vec::new();

    while let Some(command) = proof_iter.next() {
        match command {
            ProofCommand::Assume { id, term } => {
                ctx.deps
                    .insert(normalize_name(&id), (ctx.index, depth, HashSet::new()));

                proof_steps.push(f(
                    id.into(),
                    Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(vec![
                        Term::from(term),
                    ]))))),
                    vec![ProofStep::Admit],
                ))
            }
            ProofCommand::Step(AstProofStep {
                id,
                clause,
                premises,
                rule,
                args,
                discharge: _,
            }) if rule == "resolution" || rule == "th_resolution" => {
                ctx.deps
                    .insert(normalize_name(&id), (ctx.index, depth, HashSet::new()));

                let ps: HashSet<usize> = premises
                    .into_iter()
                    .map(|p| normalize_name(proof_iter.get_premise_id(*p)))
                    .collect_vec()
                    .into_iter()
                    .map(|p| ctx.deps.get(&p).unwrap().0)
                    .collect::<HashSet<_>>();

                ctx.deps.entry(normalize_name(id)).and_modify(|v| v.2 = ps);

                println!("ID = {}", id);

                let proof = translate_resolution(proof_iter, premises, args)?;

                let clauses = Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(
                    clause.into_iter().map(|a| Term::from(a)).collect(),
                )))));

                proof_steps.push(f(normalize_name(id), clauses, proof));
            }
            ProofCommand::Step(AstProofStep {
                id, clause, premises: _, rule, args, ..
            }) if rule == "rare_rewrite" => {
                ctx.deps
                    .insert(normalize_name(&id), (ctx.index, depth, HashSet::new()));

                let terms: Vec<Term> = clause.into_iter().map(|a| Term::from(a)).collect();

                let proof_script = translate_rare_simp(args);

                let step = f(
                    normalize_name(id),
                    Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(terms))))),
                    proof_script.0,
                );

                proof_steps.push(step);
            }
            ProofCommand::Step(AstProofStep { id, clause, rule, .. }) if rule.contains("simp") => {
                ctx.deps
                    .insert(normalize_name(&id), (ctx.index, depth, HashSet::new()));
                let terms: Vec<Term> = clause.into_iter().map(|a| Term::from(a)).collect();

                let proof_script = translate_simplify_step(rule);

                let step = f(
                    normalize_name(id),
                    Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(terms))))),
                    proof_script.0,
                );
                proof_steps.push(step);
            }
            ProofCommand::Step(AstProofStep {
                id, clause, premises, rule, args, ..
            }) => {
                ctx.deps
                    .insert(normalize_name(&id), (ctx.index, depth, HashSet::new()));

                let ps = premises
                    .into_iter()
                    .map(|p| normalize_name(proof_iter.get_premise_id(*p)))
                    .collect_vec()
                    .into_iter()
                    .map(|p| ctx.deps.get(&p).unwrap().0)
                    .collect::<HashSet<_>>();

                ctx.deps.entry(normalize_name(&id)).and_modify(|v| v.2 = ps);

                let step = translate_tautology(proof_iter, clause, premises, rule, args);

                let clause = clause
                    .into_iter()
                    .map(|term| ctx.get_or_convert(term))
                    .collect();

                if let Some(step) = step {
                    proof_steps.push(f(
                        normalize_name(id),
                        Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(clause))))),
                        step?.0,
                    ));
                }

                // Iteration is flatten with the ProofIter, so we need to break the looping if we
                // are in a subproof because the Subproof case use a recursive call.
                if proof_iter.is_end_step() {
                    break;
                }
            }
            ProofCommand::Subproof(Subproof { commands, args, .. }) => {
                let (id, clause, subproof, deps) = translate_subproof(
                    ctx,
                    proof_iter,
                    commands.as_slice(),
                    args.into_iter()
                        .filter(|a| matches!(a, AnchorArg::Assign(_, _)))
                        .map(|a| unwrap_match!(a, AnchorArg::Assign(s, t) => (s, t)))
                        .collect_vec(),
                    depth + 1,
                )?;

                ctx.deps
                    .insert(normalize_name(&id), (ctx.index, depth, HashSet::new()));

                let keys = deps.keys().collect::<HashSet<_>>();
                let keys2 = ctx.deps.keys().collect::<HashSet<_>>();
                let diff = keys.difference(&keys2);

                let dependencies_in_subproofs = diff
                    .map(|k| deps.get(k.as_str()).unwrap())
                    .map(|(_, _, ds)| {
                        ds.into_iter()
                            .filter(|index| {
                                deps.iter()
                                    .nth(**index)
                                    .is_some_and(|(_, (_, depth, _))| *depth == 0)
                            })
                            .map(|u| *u)
                            .collect::<HashSet<usize>>()
                    })
                    .reduce(|acc, e| acc.union(&e).map(|u| *u).collect::<HashSet<usize>>());

                if let Some(deps_subproof) = dependencies_in_subproofs {
                    ctx.deps
                        .entry(normalize_name(&id))
                        .and_modify(|(_, _, ds)| ds.extend(deps_subproof.iter()));
                }

                proof_steps.push(f(
                    normalize_name(id),
                    Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(clause))))),
                    subproof,
                ));
            }
        };
        ctx.index += 1;
    }

    Ok(proof_steps)
}