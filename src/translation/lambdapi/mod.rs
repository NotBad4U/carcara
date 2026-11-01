use crate::ast::{
    AnchorArg, Binder, Operator, ProblemPrelude, Proof as ProofElaborated, ProofCommand,
    ProofIter,
    ProofStep as AstProofStep, Rc, Sort, Subproof, Term as AletheTerm, polyeq,
    pool::{self, PrimitivePool, TermPool},
};
use indexmap::IndexMap;
use itertools::Itertools;
use thiserror::Error;
use try_match::unwrap_match;

use std::{
    collections::HashSet,
    ops::Deref,
    time::Duration,
    vec,
};

pub mod goal;
pub mod library;
pub mod logic;
#[macro_use]
pub mod syntax;

pub mod rules;

use logic::Features;
use rules::{get_premises_clause, unary_clause_to_prf};
use syntax::*;

#[derive(Debug, Error)]
pub enum TranslatorError {
    #[error("the pivot is not in the clause")]
    PivotNotInClause,
    #[error("the premises are incorrect")]
    PremisesError,
    #[error("rule `{0}` is not supported by the Lambdapi backend")]
    UnsupportedRule(String),
    #[error("RARE rule `{0}` is not supported by the Lambdapi backend")]
    UnsupportedRareRule(String),
    #[error(
        "the proof uses both integer and real arithmetic, but `alethe.lia` and \
         `alethe.lra` cannot be opened together"
    )]
    MixedArithmetic,
}

pub type TradResult<T> = Result<T, TranslatorError>;

#[derive(Default)]
pub struct Config {
    pub no_elab: bool,
    pub why3: bool,
    /// Emit `admit` for rules the backend does not implement instead of
    /// failing with [`TranslatorError::UnsupportedRule`].
    pub admit_unsupported: bool,
    /// Print every term in full instead of naming its closed subterms. Slower
    /// to check and much bigger: the A/B knob for the sharing, and the readable
    /// form when a folded goal breaks a script.
    pub no_sharing: bool,
}

/// The term-sharing state of one translation.
///
/// Every closed subterm of the proof -- no variable outside the problem's
/// declarations -- is a `symbol p_N ≔ …;` definition in the prelude, created the
/// first time the term is converted (`syntax::term::conv`), with a body made of
/// the names of its own closed subterms. Statements and scripts refer to terms by
/// these names only, so the file is a DAG rather than a tree, and Lambdapi
/// compares two occurrences of a term by symbol identity. The keys are pool
/// terms: the pool hash-conses them and `Rc` compares by pointer.
#[derive(Default)]
pub struct Context {
    /// The name of every closed subterm converted so far, in creation order,
    /// which is definition order: a term is named after its children.
    pub names: IndexMap<Rc<AletheTerm>, String>,
    /// `symbol p_N ≔ …;`, one per entry of `names`, in the same order.
    pub definitions: Vec<Command>,
    pub global_variables: HashSet<Rc<AletheTerm>>,
    /// Identifiers the file declares otherwise -- the problem's sorts and
    /// functions, the step ids -- which a name must not collide with. Nothing
    /// stops a problem from declaring a function called `p_1`.
    pub reserved: HashSet<String>,
    /// The last `p_N` handed out.
    next_name: usize,
    /// `Config::no_sharing`.
    pub no_sharing: bool,
}

impl Context {
    /// The Lambdapi term for `term`, with its closed subterms named. See
    /// [`term::conv`].
    pub fn name(&mut self, term: &Rc<AletheTerm>) -> Term {
        term::conv(term, self)
    }

    /// [`Self::name`] of each literal of a clause.
    pub fn clause_terms(&mut self, terms: &[Rc<AletheTerm>]) -> Vec<Term> {
        terms.iter().map(|t| self.name(t)).collect()
    }

    /// Record `body` as the definition of the closed term `term` and return its
    /// name. The term may already have one: `conv` bypasses the memo under a
    /// binder, where a term counts as closed only once it is known not to
    /// mention a bound variable.
    pub(crate) fn define(&mut self, term: &Rc<AletheTerm>, body: Term) -> Term {
        if let Some(name) = self.names.get(term) {
            return Term::TermId(name.clone());
        }
        let name = loop {
            self.next_name += 1;
            let name = format!("p_{}", self.next_name);
            if !self.reserved.contains(&name) {
                break name;
            }
        };
        self.definitions
            .push(Command::Definition(name.clone(), vec![], None, Some(body)));
        self.names.insert(term.clone(), name.clone());
        Term::TermId(name)
    }

    /// Every name the Lambdapi form of `terms` mentions, directly or through
    /// the body of another name, parents before children.
    ///
    /// For the scripts that `rewrite` the goal syntactically after unfolding its
    /// names: `simplify p_N` exposes one body, the names in that body can only
    /// be unfolded once it is exposed, and Lambdapi rejects a `simplify` of a
    /// name the goal does not mention. So this follows what is printed rather
    /// than the Alethe term (a subterm under a shadowing binder stays inline),
    /// and a parent comes before its children: children are named before
    /// parents, so the creation index in descending order is such an order.
    pub fn names_under(&mut self, terms: &[Rc<AletheTerm>]) -> Vec<String> {
        let converted = self.clause_terms(terms);
        let index_of: std::collections::HashMap<&str, usize> = self
            .names
            .values()
            .enumerate()
            .map(|(i, n)| (n.as_str(), i))
            .collect();
        let indices_in = |term: &Term| {
            let mut used = HashSet::new();
            goal::collect_term(term, &mut used, &HashSet::new());
            used.iter()
                .filter_map(|n| index_of.get(n.as_str()).copied())
                .collect::<Vec<usize>>()
        };
        let mut found = HashSet::new();
        let mut todo: Vec<usize> = converted.iter().flat_map(indices_in).collect();
        while let Some(i) = todo.pop() {
            if found.insert(i)
                && let Command::Definition(_, _, _, Some(body)) = &self.definitions[i]
            {
                todo.extend(indices_in(body));
            }
        }
        let mut indices: Vec<usize> = found.into_iter().collect();
        indices.sort_unstable_by(|a, b| b.cmp(a));
        indices.into_iter().map(|i| self.names[i].clone()).collect()
    }
}

/// The invariants of the sharing table: one definition per name, in creation
/// order, and a body that mentions only names defined before it, so that the
/// prelude is in dependency order. Checked in debug builds and by the tests.
pub(crate) fn sharing_invariants(ctx: &Context) -> Result<(), String> {
    if ctx.definitions.len() != ctx.names.len() {
        return Err(format!(
            "{} definitions for {} names",
            ctx.definitions.len(),
            ctx.names.len()
        ));
    }
    let index_of: std::collections::HashMap<&str, usize> = ctx
        .names
        .values()
        .enumerate()
        .map(|(i, n)| (n.as_str(), i))
        .collect();
    for (i, (def, name)) in ctx.definitions.iter().zip(ctx.names.values()).enumerate() {
        let Command::Definition(id, _, None, Some(body)) = def else {
            return Err(format!("definition {i} is not `symbol {name} ≔ …`: {def:?}"));
        };
        if id != name {
            return Err(format!("definition {i} is `{id}`, the name is `{name}`"));
        }
        let mut used = HashSet::new();
        goal::collect_term(body, &mut used, &HashSet::new());
        if let Some(later) = used
            .iter()
            .find(|u| index_of.get(u.as_str()).is_some_and(|&j| j >= i))
        {
            return Err(format!("the body of `{name}` mentions `{later}`, defined after it"));
        }
    }
    Ok(())
}

/// The ids of every command, subproofs included, as `normalize_name` prints them.
fn command_ids(commands: &[ProofCommand], ids: &mut HashSet<String>) {
    for command in commands {
        match command {
            ProofCommand::Assume { id, .. } => {
                ids.insert(normalize_name(id));
            }
            ProofCommand::Step(step) => {
                ids.insert(normalize_name(&step.id));
            }
            ProofCommand::Subproof(sp) => command_ids(&sp.commands, ids),
        }
    }
}


fn translate_sort_function(sort: &Sort, used: &mut Features) -> Term {
    match sort {
        Sort::Bool => omicron(),
        Sort::Int => {
            // `int` is `Stdlib.Z.int`, and `Stdlib.Z` reaches a generated proof
            // only through `alethe.lia`. Naming the sort is therefore as much of a
            // dependency on the integer layer as using a `la_*` rule is.
            *used |= Features::INT;
            "int".into()
        }
        Sort::Real => {
            // Likewise `real` is `alethe.real`'s carrier, reached through `alethe.lra`.
            *used |= Features::REAL;
            "real".into()
        }
        Sort::Function(params) => {
            let sorts = params
                .iter()
                .map(|s| translate_sort_function(s, used))
                .collect_vec();

            sorts
                .into_iter()
                .reduce(|acc, e| Term::Sort(BuiltinSort::Arrow(Box::new(acc), Box::new(e))))
                .unwrap()
        }
        Sort::Atom(a, args) => {
            if args.is_empty() {
                a.as_ref().into()
            } else {
                let mut args: Vec<Term> = args
                    .iter()
                    .map(|s| translate_sort_function(s, used))
                    .collect_vec();
                let mut sort = vec![a.as_ref().into()];
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
fn translate_prelude(prelude: ProblemPrelude, used: &mut Features) -> Vec<Command> {
    let mut sort_declarations_symbols = prelude
        .sort_declarations
        .into_iter()
        .map(|(id, arity)| {
            let sorts = itertools::repeat_n(set(), arity + 1).collect_vec();
            Command::Definition(id, vec![], Some(Term::Function(sorts)), None)
        })
        .collect::<Vec<Command>>();

    let mut function_declarations_symbols = prelude
        .function_declarations
        .into_iter()
        .map(|(id, sort)| {
            let sort = tau(translate_sort_function(&sort, used));

            Command::Definition(id, vec![], Some(sort), None)
        })
        .collect::<Vec<Command>>();

    sort_declarations_symbols.append(&mut function_declarations_symbols);

    sort_declarations_symbols
}


/// Which arithmetic carriers the proof names anywhere.
///
/// An integer literal is emitted as `Stdlib.Z.<n>` and a real one as `lit (…)`, and
/// `Stdlib.Z` and `alethe.real` are required by a generated proof only through
/// `alethe.lia` and `alethe.lra`. Gating those modules on the `la_*` and `arith-*`
/// rules alone is not enough: a proof can carry a constant --
/// `(step t1 (cl (= 1 1)) :rule refl)` -- without ever reaching an arithmetic rule,
/// and would then print a numeral no module in its header can scope.
///
/// Sorts are handled separately, in `translate_sort_function`.
fn carriers_used(proof: &ProofElaborated) -> Features {
    fn of_sort(sort: &Sort) -> Features {
        match sort {
            Sort::Int => Features::INT,
            Sort::Real => Features::REAL,
            _ => Features::EMPTY,
        }
    }

    fn in_term(term: &Rc<AletheTerm>, seen: &mut HashSet<*const AletheTerm>) -> Features {
        if !seen.insert(Rc::as_ptr(term)) {
            return Features::EMPTY;
        }
        let all = |ts: &[Rc<AletheTerm>], seen: &mut _| {
            ts.iter().fold(Features::EMPTY, |acc, t| acc.union(in_term(t, seen)))
        };
        match term.deref() {
            AletheTerm::Const(c) => of_sort(&c.sort()),
            AletheTerm::Var(_, sort) => of_sort(sort),
            AletheTerm::App(f, args) => in_term(f, seen).union(all(args, seen)),
            AletheTerm::Op(_, args) | AletheTerm::AsOp(_, _, args) => all(args, seen),
            AletheTerm::Binder(_, bs, t) => bs
                .iter()
                .fold(in_term(t, seen), |acc, (_, sort)| acc.union(of_sort(sort))),
            AletheTerm::Let(bs, t) => bs
                .iter()
                .fold(in_term(t, seen), |acc, (_, v)| acc.union(in_term(v, seen))),
            AletheTerm::Match(t, cases) => cases
                .iter()
                .fold(in_term(t, seen), |acc, c| acc.union(in_term(&c.body, seen))),
            AletheTerm::ParamOp { op_args, args, .. } => all(op_args, seen).union(all(args, seen)),
        }
    }

    fn in_commands(cs: &[ProofCommand], seen: &mut HashSet<*const AletheTerm>) -> Features {
        cs.iter().fold(Features::EMPTY, |acc, c| {
            acc.union(match c {
                ProofCommand::Assume { term, .. } => in_term(term, seen),
                // Only the clause. A step's `:args` are not all terms: for `and`,
                // `not_or`, `and_pos` and `or_neg` they are clause and conjunct
                // indices, which arrive as `Constant::Integer` but are emitted as
                // `Stdlib.Nat.n` and say nothing about ℤ. Counting them put `lia`
                // -- and its admits -- into pure QF_UF proofs. The args that really
                // are arithmetic terms belong to `la_generic`, which reports its
                // carrier itself; anything instantiated into a formula shows up in
                // a clause.
                ProofCommand::Step(s) => s
                    .clause
                    .iter()
                    .fold(Features::EMPTY, |acc, t| acc.union(in_term(t, seen))),
                ProofCommand::Subproof(sp) => {
                    let args = sp.args.iter().fold(Features::EMPTY, |acc, a| {
                        acc.union(match a {
                            AnchorArg::Variable((_, sort)) => of_sort(sort),
                            AnchorArg::Assign(_, t) => in_term(t, seen),
                        })
                    });
                    args.union(in_commands(&sp.commands, seen))
                }
            })
        })
    }

    let mut seen = HashSet::new();
    proof
        .constant_definitions
        .iter()
        .fold(Features::EMPTY, |acc, (_, t)| acc.union(in_term(t, &mut seen)))
        .union(in_commands(&proof.commands, &mut seen))
}

pub fn produce_lambdapi_proof(
    prelude: ProblemPrelude,
    proof_elaborated: ProofElaborated,
    mut pool: pool::PrimitivePool,
    config: Config,
) -> TradResult<ProofFile> {
    let mut proof_file = ProofFile::new();
    let logic = prelude.logic.clone();

    let global_variables: HashSet<_> = prelude
        .function_declarations
        .iter()
        .map(|var| pool.add(var.clone().into()))
        .collect();

    let declared = logic::features_of_logic(logic.as_deref());
    // What the *steps* turn out to need, accumulated as they are translated. It
    // starts empty rather than from `declared`: `logic::modules` adds what a
    // standard logic declares itself, and keeping the two apart is what lets it
    // refuse to open both arithmetic carriers on a declaration alone.
    let mut features = Features::EMPTY;

    features |= carriers_used(&proof_elaborated);

    proof_file.definitions = translate_prelude(prelude, &mut features);

    let mut reserved: HashSet<String> = proof_file
        .definitions
        .iter()
        .filter_map(|c| match c {
            Command::Definition(name, ..) | Command::Symbol(_, name, ..) => Some(name.clone()),
            Command::RequireOpen(_) | Command::Rule(..) => None,
        })
        .collect();
    command_ids(&proof_elaborated.commands, &mut reserved);

    let mut context = Context {
        global_variables,
        reserved,
        no_sharing: config.no_sharing,
        ..Default::default()
    };

    let mut commands = translate_commands(
        &mut context,
        &mut proof_elaborated.iter(),
        &mut pool,
        &config,
        &mut features,
        |id, t, ps| {
            let modifier = ps.is_some().then_some(Modifier::Opaque);
            Command::Symbol(modifier, normalize_name(id), vec![], t, ps.map(Proof))
        },
    )?;

    // Stop postulating the problem's last assertion and end on what the proof is
    // actually for. Leaves `commands` alone, and the file ending at `π̇ □`, when the
    // proof has no top-level assume or does not close the empty clause.
    goal::discharge(&mut commands, &proof_elaborated, &mut context);

    // After `discharge`, which may still name a term, and after the declarations,
    // which the bodies refer to.
    debug_assert_eq!(sharing_invariants(&context), Ok(()));
    proof_file.definitions.append(&mut context.definitions);

    proof_file.content.extend(commands);

    report_logic(logic.as_deref(), declared, features);
    if features.contains(Features::INT.union(Features::REAL)) {
        return Err(TranslatorError::MixedArithmetic);
    }
    proof_file.requires = logic::modules(declared, features)
        .into_iter()
        .map(|m| Command::RequireOpen(m.path().to_owned()))
        .collect();

    Ok(proof_file)
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

/// Translate (anchor :step ti) and its steps
/// A subproof is translated into an opaque symbol
/// added to the prelude of the file.
fn translate_subproof<'a>(
    context: &mut Context,
    iter: &mut ProofIter<'a>,
    commands: &[ProofCommand],
    assignment_args: Vec<(&(String, Rc<Sort>), &Rc<AletheTerm>)>,
    pool: &mut PrimitivePool,
    config: &Config,
    features: &mut Features,
) -> TradResult<(String, Vec<Term>, Vec<ProofStep>)> {
    let subproof = commands.last().unwrap();

    //Get the last step of the proof
    let (id, clause, rule) = unwrap_match!(
        subproof,
        ProofCommand::Step(AstProofStep { id, clause, rule,.. }) => (normalize_name(id), clause, rule)
    );

    let clause = context.clause_terms(clause);

    let mut proof_cmds = translate_commands(context, iter, pool, config, features, |id, t, ps| {
        ProofStep::Have(normalize_name(id), t, ps.unwrap_or(admit()))
    })?;

    proof_cmds
        .iter_mut()
        .filter(|cmd| matches!(cmd, ProofStep::Have(_, _, _)))
        .for_each(|cmd| {
            if let ProofStep::Have(name, cl, steps) = cmd {
                cl.visit(&assignment_args);
                *cmd = ProofStep::Have((*name).clone(), cl.clone(), steps.clone());
            }
        });

    // The anchor variables `bind` assumes, as bare identifiers: not names.
    let assignment_args = assignment_args
        .into_iter()
        .map(|(_, term)| Term::from(term))
        .collect_vec();

    let subproof_have_wrapper = if rule == "bind" {
        let mut proof = vec![];

        let last_step_id = unwrap_match!(commands.get(commands.len() - 2), Some(ProofCommand::Step(AstProofStep{id, ..})) => normalize_name(id));

        let bind_lemma = match subproof.clause().first().expect("clause is empty").deref() {
            AletheTerm::Op(Operator::Equals, args)
                if matches!(args[0].deref(), AletheTerm::Binder(Binder::Forall, _, _))
                    && matches!(args[1].deref(), AletheTerm::Binder(Binder::Forall, _, _)) =>
            {
                "bind_∀"
            }
            AletheTerm::Op(Operator::Equals, args)
                if matches!(args[0].deref(), AletheTerm::Binder(Binder::Exists, _, _))
                    && matches!(args[1].deref(), AletheTerm::Binder(Binder::Exists, _, _)) =>
            {
                "bind_∃"
            }
            _ => unreachable!(),
        };

        // `bind_∀` / `bind_∃` live in `quant.lp`. This wrapper is built here rather
        // than through the rule dispatch table, which reports no feature for
        // `bind`, so the dependency has to be recorded at the point of use.
        *features |= Features::QUANT;

        proof.push(ProofStep::Apply(Term::from("∨ᵢ₁"), SubProofs(None)));
        assignment_args.into_iter().for_each(|term| {
            proof.push(ProofStep::Apply(Term::from(bind_lemma), SubProofs(None)));
            proof.push(ProofStep::Assume(vec![format!("{}", term)]));
        });
        proof.append(&mut proof_cmds);

        proof.push(ProofStep::Apply(
            terms![Term::from("π̇ₗ"), Term::from(last_step_id)],
            SubProofs(None),
        ));

        proof
    } else if rule == "sko_forall" {
        let last_step_id = unwrap_match!(commands.last(), Some(ProofCommand::Step(AstProofStep{id, ..})) => normalize_name(id));

        // end of the script
        proof_cmds.append(&mut lambdapi! {
            apply "∨ᵢ₁";
            apply "π̇ₗ" (@last_step_id.into());
        });
        proof_cmds
    } else {
        proof_cmds
    };

    Ok((id, clause, subproof_have_wrapper))
}



fn translate_commands<'a, F, T>(
    ctx: &mut Context,
    proof_iter: &mut ProofIter<'a>,
    pool: &mut PrimitivePool,
    config: &Config,
    features: &mut Features,
    f: F,
) -> TradResult<Vec<T>>
where
    F: Fn(String, Term, Option<Vec<ProofStep>>) -> T,
{
    let mut proof_steps = Vec::new();

    while let Some(command) = proof_iter.next() {
        match command {
            ProofCommand::Assume { id, term } => proof_steps.push(f(
                id.into(),
                term::clauses(vec![ctx.name(term)]),
                None,
            )),
            ProofCommand::Step(AstProofStep {
                id, clause, premises, rule, args, ..
            }) => {
                let (script, used) = rules::translate_step(
                    ctx, proof_iter, pool, clause, premises, rule, args, config,
                )?;
                *features |= used;

                let terms = ctx.clause_terms(clause);

                if let Some(script) = script {
                    proof_steps.push(f(
                        normalize_name(id),
                        Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(terms))))),
                        Some(script),
                    ));
                }

                // Iteration is flattened by the ProofIter, so the loop must stop at the
                // last step of a subproof: the Subproof arm recurses into it.
                if proof_iter.is_end_step() {
                    break;
                }
            }
            ProofCommand::Subproof(Subproof { commands, args, .. }) => {
                let (_id, clause, subproof) = translate_subproof(
                    ctx,
                    proof_iter,
                    commands.as_slice(),
                    args.iter()
                        .filter(|a| matches!(a, AnchorArg::Assign(_, _)))
                        .map(|a| unwrap_match!(a, AnchorArg::Assign(s, t) => (s, t)))
                        .collect_vec(),
                    pool,
                    config,
                    features,
                )?;

                let sub = commands.last().unwrap();

                //Get the last step of the proof
                let (id, cl, rule) = unwrap_match!(
                    sub,
                    ProofCommand::Step(AstProofStep { id, clause, rule,.. }) => (normalize_name(id), clause, rule)
                );

                if rule.contains("subproof") {
                    //HACK: we convert all the Have proof step into symbols to improve lambdapi check performance.
                    // We only do this for proof that use the `subproof` rule because `bind` and `sko_forall` for example
                    // creates temporary free variable in their context making the split of steps into `symbol` instead of `have` impossible.
                    // Lambdapi seems to be very slow on proof that have a large context.
                    let res = subproof.into_iter().map(|s| unwrap_match!(s, ProofStep::Have(id, r#type, proof) =>  f(id, r#type, Some(proof)))).collect_vec();
                    proof_steps.extend(res);

                    let discharge = unwrap_match!(commands.last(), Some(ProofCommand::Step(AstProofStep{id: _, clause:_, rule:_, premises:_, args:_, discharge})) => discharge);

                    let premises_discharge = get_premises_clause(proof_iter, discharge);

                    let mut script = std::iter::repeat_n(
                        ProofStep::Apply(Term::TermId("∨ᵢ₂".to_owned()), SubProofs(None)),
                        premises_discharge.len(),
                    )
                    .collect_vec();

                    let (psy_id, trailing_false_on_last_step) = unwrap_match!(commands.get(commands.len() - 2), Some(ProofCommand::Step(AstProofStep{id, clause, ..})) => {
                        (normalize_name(id), clause.iter().last().is_some_and(|t| t.is_bool_false()))
                    });

                    let trailing_false_on_conclusion_clause =
                        cl.iter().last().is_some_and(|t| t.is_bool_false());

                    // Some subproof can add a trailing false in their clause and also for the step just before the clonclusion of the subproof.
                    // We detect if there is a trailing false if the number of the element in the clause and the discharge are different
                    if trailing_false_on_conclusion_clause && trailing_false_on_last_step {
                        script.push(ProofStep::Apply(psy_id.as_str().into(), SubProofs(None)));
                    } else if trailing_false_on_conclusion_clause {
                        // Case with a trailing false
                        script.push(ProofStep::Apply(
                            Term::TermId("∨ᵢ₂".to_owned()),
                            SubProofs(None),
                        ));
                        script.push(ProofStep::Apply(psy_id.as_str().into(), SubProofs(None)));
                    } else if trailing_false_on_last_step {
                        // Case with a trailing false
                        script.push(ProofStep::Apply(
                            Term::TermId("∨ᵢ₁".to_owned()),
                            SubProofs(None),
                        ));
                        script.push(ProofStep::Apply(
                            unary_clause_to_prf(psy_id.as_str()),
                            SubProofs(None),
                        ));
                    } else {
                        // Case without a trailing false
                        script.push(ProofStep::Apply(
                            Term::TermId("∨ᵢ₁".to_owned()),
                            SubProofs(None),
                        ));

                        script.push(ProofStep::Apply(
                            unary_clause_to_prf(psy_id.as_str()),
                            SubProofs(None),
                        ));
                    }

                    proof_steps.push(f(
                        normalize_name(id),
                        Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(clause))))),
                        Some(script),
                    ));
                } else {
                    proof_steps.push(f(
                        normalize_name(id),
                        Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(clause))))),
                        Some(subproof),
                    ));
                }
            }
        };
    }

    Ok(proof_steps)
}

#[cfg(test)]
mod tests_translation {
    use super::test_macros::parse_test_instance;
    use super::*;

    #[test]
    fn test_resolution() {
        let problem = "
           (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
        ";
        let proof = "
            (assume a4 (not (= a a)))
            (step t1 (cl (= a a) (= b b)) :rule hole)
            (step t2 (cl (= c c) (not (= a a))) :rule hole)
            (step t3 (cl (= b b) (= c c)) :rule resolution :premises (t1 t2) :args ((= a a) true))
        ";
        let (problem, proof, _, mut pool) = parse_test_instance(problem, proof).unwrap();

        let global_variables: HashSet<_> = problem
            .prelude
            .function_declarations
            .iter()
            .map(|var| pool.add(var.clone().into()))
            .collect();

        let mut ctx = Context {
            global_variables,
            ..Default::default()
        };

        let res = translate_commands(&mut ctx, &mut proof.iter(), &mut pool, &Config::default(), &mut Features::EMPTY, |id, t, ps| {
            let modifier = ps.is_some().then_some(Modifier::Opaque);
            Command::Symbol(modifier, normalize_name(id), vec![], t, ps.map(Proof))
        })
        .expect("translate trans");

        let _: Command = res.last().unwrap().clone();

        //println!("{}", t3);
    }

    fn translate(problem: &str, proof: &str, config: Config) -> TradResult<ProofFile> {
        let (problem, proof, _, pool) = parse_test_instance(problem, proof).unwrap();
        let elaborated = ProofElaborated {
            constant_definitions: proof.constant_definitions.clone(),
            commands: proof.commands.clone(),
            filename: proof.filename.clone(),
        };
        produce_lambdapi_proof(problem.prelude, elaborated, pool, config)
    }

    /// The `require` header of a translated proof, as module paths.
    fn requires_of(problem: &str, proof: &str) -> Vec<String> {
        translate(problem, proof, Config::default())
            .expect("translation failed")
            .requires
            .iter()
            .map(|c| match c {
                Command::RequireOpen(m) => m.clone(),
                other => panic!("not a require: {other:?}"),
            })
            .collect()
    }

    /// `lia` and `lra` rebind the decimal notation to different carriers, so a
    /// header carrying both leaves every numeral ambiguous. An unrecognised logic
    /// used to declare every feature, and seeding the used set from it opened
    /// both. `logic.rs` covers `modules` in isolation, so only a test at this
    /// level catches the seeding.
    #[test]
    fn an_unrecognised_logic_does_not_open_the_rational_carrier() {
        // `UF` is not among the 25 standard logics, and this problem has no
        // real arithmetic anywhere -- only an uninterpreted sort.
        let requires = requires_of(
            "(set-logic UF)
             (declare-sort U 0)
             (declare-fun p (U) Bool)
             (declare-fun a () U)",
            "(assume h1 (p a))
             (step t1 (cl (p a)) :rule hole :premises (h1))",
        );
        assert!(
            !requires.iter().any(|m| m == "alethe.lra"),
            "unrecognised logic dragged in the rational carrier: {requires:?}"
        );
        assert!(
            !(requires.iter().any(|m| m == "alethe.lia")
                && requires.iter().any(|m| m == "alethe.lra")),
            "lia and lra must not be opened together: {requires:?}"
        );
    }

    /// An integer literal alone has to pull in the integer layer.
    ///
    /// `Stdlib.Z.<n>` -- and the `int` sort name -- resolve only if the file
    /// required `Stdlib.Z`, which a generated proof reaches only through
    /// `alethe.lia`. Gating that on the `la_*`/`arith-*` rules leaves a proof that
    /// mentions an integer without ever taking an arithmetic step printing a
    /// numeral no module in its header can scope.
    #[test]
    fn an_integer_literal_opens_the_integer_layer() {
        let requires = requires_of(
            "(set-logic QF_UF)
             (declare-fun p (Int) Bool)
             (declare-fun a () Int)",
            "(assume h1 (p a))
             (step t1 (cl (= 1 1)) :rule refl)",
        );
        assert!(
            requires.iter().any(|m| m == "alethe.lia"),
            "an integer literal did not open the integer layer: {requires:?}"
        );
    }

    #[test]
    fn a_real_literal_opens_the_real_layer() {
        let requires = requires_of(
            "(set-logic QF_UF)
             (declare-fun p (Real) Bool)
             (declare-fun a () Real)",
            "(assume h1 (p a))
             (step t1 (cl (= a 1.0)) :rule refl)",
        );
        assert!(
            requires.iter().any(|m| m == "alethe.lra"),
            "a real literal did not open the real layer: {requires:?}"
        );
        assert!(
            !requires.iter().any(|m| m == "alethe.lia"),
            "a real proof opened the integer layer: {requires:?}"
        );
    }

    /// A standard logic opens its theory modules, each with its `rare/`
    /// companion, even when no step needs them.
    #[test]
    fn a_standard_logic_opens_its_theory_modules() {
        let requires = requires_of(
            "(set-logic QF_LIA)
             (declare-fun p () Bool)",
            "(assume h1 p)
             (step t1 (cl p) :rule hole :premises (h1))",
        );
        assert_eq!(
            requires,
            ["alethe.core", "alethe.prop", "alethe.rare.prop", "alethe.lia", "alethe.rare.lia"]
        );
    }

    /// A RARE rule with no proof in the backend fails the translation, instead of
    /// emitting `apply <name>` for a lemma the library may not declare, which
    /// would only surface at `lambdapi check`.
    #[test]
    fn an_unknown_rare_rule_is_unsupported() {
        let problem = "(set-logic QF_UF)
             (declare-fun p () Bool)";
        let proof = r#"(step t1 (cl (= (or (not (= p p)) p) p)) :rule rare_rewrite :args ("or-not-refl" p))"#;
        match translate(problem, proof, Config::default()) {
            Err(TranslatorError::UnsupportedRareRule(name)) => assert_eq!(name, "or-not-refl"),
            Err(e) => panic!("wrong error: {e}"),
            Ok(_) => panic!("an unknown RARE rule was translated"),
        }
        let admitting = Config { admit_unsupported: true, ..Config::default() };
        assert!(
            translate(problem, proof, admitting).is_ok(),
            "--admit-unsupported did not admit an unknown RARE rule"
        );
    }

    fn content_of(problem: &str, proof: &str) -> Vec<Command> {
        translate(problem, proof, Config::default())
            .expect("translation failed")
            .content
    }

    /// A `hole` step is the solver's own gap, so it is admitted under the
    /// library's `#hole` name rather than with the plain `admit` that marks a
    /// rule the translator does not handle: `grep` can then count the two apart.
    #[test]
    fn a_solver_hole_is_admitted_under_its_own_name() {
        let content = content_of(
            "(set-logic QF_UF)
             (declare-fun p () Bool)
             (declare-fun q () Bool)",
            "(assume h1 p)
             (step t1 (cl (not p) q) :rule hole)
             (step t2 (cl q) :rule resolution :premises (h1 t1) :args (p true))",
        );
        let script = content
            .iter()
            .find_map(|c| match c {
                Command::Symbol(_, name, _, _, Some(Proof(steps))) if name == "t1" => Some(steps),
                _ => None,
            })
            .expect("t1 was not translated to a proved symbol");
        assert_eq!(script, &hole(), "a hole step is not `eval #hole`: {script:?}");
        assert!(!script.contains(&ProofStep::Admit));
    }

    /// The refutation's last assertion is discharged, not postulated.
    ///
    /// Emitting every `assume` as an axiom makes the axiom set inconsistent by
    /// construction -- the negated goal is among them -- so a concluding `π G` read
    /// off the empty clause would prove nothing. The last assertion has to stop
    /// being an axiom for the final statement to mean anything.
    #[test]
    fn the_last_assertion_is_discharged_not_postulated() {
        let content = content_of(
            "(set-logic QF_UF)
             (declare-fun p () Bool)",
            "(assume h1 p)
             (assume h2 (not p))
             (step t1 (cl) :rule resolution :premises (h1 h2) :args (p true))",
        );

        assert!(
            !content.iter().any(
                |c| matches!(c, Command::Symbol(_, name, _, _, None) if name == "h2")
            ),
            "the discharged assertion is still an axiom: {content:?}"
        );
        // `h1` is not the last assertion, so it stays a hypothesis of the theory.
        assert!(
            content
                .iter()
                .any(|c| matches!(c, Command::Symbol(_, name, _, _, None) if name == "h1")),
            "an assertion other than the last one was discharged: {content:?}"
        );

        // `(not p)` is a negation, so the theorem states `p` itself rather than
        // `¬ (¬ p)`, and it is named after the assertion it discharges.
        let Some(Command::Symbol(_, name, _, statement, Some(_))) = content.last() else {
            panic!("the file does not end in a proved symbol: {content:?}");
        };
        assert_eq!(name, "h2");
        assert_eq!(
            *statement,
            Term::Alethe(LTerm::ClassicProof(Box::new(Term::from("p")))),
            "expected `π p`, got {statement:?}"
        );
    }

    fn globals(problem: &crate::ast::Problem, pool: &mut PrimitivePool) -> HashSet<Rc<AletheTerm>> {
        problem
            .prelude
            .function_declarations
            .iter()
            .map(|var| pool.add(var.clone().into()))
            .collect()
    }

    fn id(s: &str) -> Term {
        Term::TermId(s.to_owned())
    }

    fn definitions_of(ctx: &Context) -> Vec<(String, Term)> {
        ctx.definitions
            .iter()
            .map(|d| match d {
                Command::Definition(name, _, None, Some(body)) => (name.clone(), body.clone()),
                other => panic!("not a `symbol p_N ≔ …`: {other:?}"),
            })
            .collect()
    }

    /// Every closed subterm is defined once, children before parents, and
    /// converting a term again yields the same name.
    #[test]
    fn closed_subterms_are_named_once_children_first() {
        let (problem, proof, _, mut pool) = parse_test_instance(
            "(declare-sort U 0) (declare-fun a () U) (declare-fun b () U) (declare-fun f (U) U)",
            "(step t1 (cl (not (= (f a) b))) :rule hole)",
        )
        .unwrap();
        let mut ctx = Context {
            global_variables: globals(&problem, &mut pool),
            ..Default::default()
        };
        let t = proof.commands[0].clause()[0].clone();

        assert_eq!(ctx.name(&t), id("p_3"));
        assert_eq!(ctx.name(&t), id("p_3"), "a second conversion allocates nothing");
        assert_eq!(
            definitions_of(&ctx),
            vec![
                ("p_1".to_owned(), Term::Terms(vec![id("f"), id("a")])),
                (
                    "p_2".to_owned(),
                    Term::Alethe(LTerm::Eq(Box::new(id("p_1")), Box::new(id("b"))))
                ),
                ("p_3".to_owned(), Term::Alethe(LTerm::Neg(Some(Box::new(id("p_2")))))),
            ]
        );
        assert_eq!(ctx.names_under(std::slice::from_ref(&t)), ["p_3", "p_2", "p_1"]);
        assert_eq!(sharing_invariants(&ctx), Ok(()));
    }

    /// Under a binder, only the subterms that mention no bound variable are
    /// named; the quantifier itself is, its own variables being bound in it.
    #[test]
    fn a_binder_names_only_what_mentions_no_bound_variable() {
        let (problem, proof, _, mut pool) = parse_test_instance(
            "(declare-sort U 0) (declare-fun a () U) (declare-fun f (U) U)",
            "(step t1 (cl (forall ((x U)) (= (f x) (f a)))) :rule hole)",
        )
        .unwrap();
        let mut ctx = Context {
            global_variables: globals(&problem, &mut pool),
            ..Default::default()
        };
        let t = proof.commands[0].clause()[0].clone();

        assert_eq!(ctx.name(&t), id("p_2"));
        let defs = definitions_of(&ctx);
        assert_eq!(defs[0], ("p_1".to_owned(), Term::Terms(vec![id("f"), id("a")])));
        let (name, body) = &defs[1];
        assert_eq!(name, "p_2");
        let Term::Alethe(LTerm::Forall(_, body)) = body else {
            panic!("the quantifier is not the body: {body:?}");
        };
        assert_eq!(
            **body,
            Term::Alethe(LTerm::Eq(
                Box::new(Term::Terms(vec![id("f"), id("x")])),
                Box::new(id("p_1"))
            )),
            "`(f x)` mentions the bound variable and stays inline"
        );
        assert_eq!(ctx.names_under(std::slice::from_ref(&t)), ["p_2", "p_1"]);
    }

    /// A bound variable shadows a declared constant of the same name: the pool
    /// term `(P x)` is closed outside the quantifier and open inside it, so the
    /// inner occurrence must not become the outer one's name.
    #[test]
    fn a_shadowing_binder_does_not_capture_a_name() {
        let (problem, proof, _, mut pool) = parse_test_instance(
            "(declare-sort U 0) (declare-fun x () U) (declare-fun P (U) Bool)",
            "(step t1 (cl (P x) (forall ((x U)) (P x))) :rule hole)",
        )
        .unwrap();
        let mut ctx = Context {
            global_variables: globals(&problem, &mut pool),
            ..Default::default()
        };
        let clause = proof.commands[0].clause().to_vec();

        assert_eq!(ctx.clause_terms(&clause), [id("p_1"), id("p_2")]);
        let (_, quantified) = &definitions_of(&ctx)[1];
        let Term::Alethe(LTerm::Forall(_, body)) = quantified else {
            panic!("the quantifier is not the body: {quantified:?}");
        };
        assert_eq!(
            **body,
            Term::Terms(vec![id("P"), id("x")]),
            "the inner `(P x)` must stay inline, not become `p_1`"
        );
    }

    /// The problem may declare `p_1` itself; the names skip it.
    #[test]
    fn names_skip_the_problems_own_identifiers() {
        let file = translate(
            "(declare-fun p_1 () Bool) (declare-fun q () Bool)",
            "(assume h1 (and p_1 q))
             (step t1 (cl (and p_1 q)) :rule hole :premises (h1))",
            Config::default(),
        )
        .expect("translation failed");
        let names = file
            .definitions
            .iter()
            .filter_map(|d| match d {
                Command::Definition(name, _, None, Some(_)) => Some(name.as_str()),
                _ => None,
            })
            .collect_vec();
        assert_eq!(names, ["p_2"], "{:?}", file.definitions);
    }

    /// `no_sharing` prints every term in full: no definition carries a body.
    #[test]
    fn no_sharing_defines_nothing() {
        let file = translate(
            "(declare-sort U 0) (declare-fun a () U) (declare-fun f (U) U)",
            "(assume h1 (= (f a) a))
             (step t1 (cl (= (f a) a)) :rule hole :premises (h1))",
            Config { no_sharing: true, ..Config::default() },
        )
        .expect("translation failed");
        assert!(
            !file
                .definitions
                .iter()
                .any(|d| matches!(d, Command::Definition(_, _, None, Some(_)))),
            "{:?}",
            file.definitions
        );
    }

    /// A proof that does not close the empty clause is left exactly as it was.
    #[test]
    fn a_proof_that_is_not_a_refutation_keeps_its_axioms() {
        let content = content_of(
            "(set-logic QF_UF)
             (declare-fun p () Bool)",
            "(assume h1 p)
             (step t1 (cl p) :rule hole :premises (h1))",
        );
        assert!(
            content
                .iter()
                .any(|c| matches!(c, Command::Symbol(_, name, _, _, None) if name == "h1")),
            "a non-refutation had its assumption discharged: {content:?}"
        );
    }
}

/// Report how the declared logic compares with what the proof actually used.
///
/// A standard logic is an over-approximation by construction (the standard has
/// no name for every feature combination), so an unused declared feature is
/// normal. The interesting direction is the other one: a rule needing a feature
/// the logic did not declare usually means the problem's `(set-logic …)` is
/// wrong.
fn report_logic(logic: Option<&str>, declared: Option<Features>, used: Features) {
    let name = logic.unwrap_or("(none)");
    match declared {
        Some(declared) => {
            let missing = used.difference(declared);
            if !missing.is_empty() {
                log::warn!(
                    "proof uses {missing:?}, which `(set-logic {name})` does not declare; \
                     the import list was widened to match"
                );
            }
        }
        None if logic.is_some_and(|l| l != "ALL") => {
            log::warn!(
                "`{name}` is not one of the 25 SMT-LIB logics; importing only what the proof uses"
            );
        }
        None => {}
    }
    let unsupported = used.unsupported();
    if !unsupported.is_empty() {
        log::warn!("proof uses {unsupported:?}, which the Lambdapi backend does not implement");
    }
}
