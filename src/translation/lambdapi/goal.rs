//! Turn the refutation into a proof of the problem's goal.
//!
//! An Alethe proof is a refutation: it derives the empty clause from the problem's
//! assertions. Translated naively every assertion becomes a Lambdapi *axiom* and the
//! file ends at `opaque symbol t42 : π̇ □`, which is `π ⊥` definitionally (`π̇ l ≔ π
//! (disj l)`, `disj □ ↪ ⊥`). That records the refutation but proves nothing about the
//! conjecture: the negated goal is postulated, so the axiom set is inconsistent and
//! any statement would follow from it.
//!
//! This module stops postulating the last assertion. It becomes a hypothesis that the
//! steps using it take as a parameter, and the file ends with a real theorem —
//! `π G` when the assertion is `(not G)`, `π (¬ A)` otherwise.
//!
//! Which assertion is discharged only decides how useful the statement is, never
//! whether it holds: from axioms `H…` together with `A` the proof derived `⊥`, so
//! `¬A` is a theorem of `H…` for any choice of `A`.

use super::*;

/// The name the discharged hypothesis is bound to inside every step that uses it.
/// Alethe step and assume ids never collide with it: they come from the solver as
/// `t12`, `a3`, or a quoted SMT-LIB symbol, and `normalize_name` only ever removes
/// characters.
const HYP: &str = "hGoal";

/// The `assume` the final theorem discharges: the last top-level one, which is the
/// problem's last `assert`.
///
/// Only depth 0 is scanned. A subproof-local assume (`t1.a0`) is already discharged
/// by the `have` block that introduces it, and is not an assertion of the problem.
pub fn discharged_assume(proof: &ProofElaborated) -> Option<(String, Rc<AletheTerm>)> {
    proof.commands.iter().rev().find_map(|c| match c {
        ProofCommand::Assume { id, term } => Some((normalize_name(id), term.clone())),
        _ => None,
    })
}

/// Is this proof a refutation -- does its last top-level step conclude the empty
/// clause? A proof that ends anywhere else is left alone.
pub fn ends_in_empty_clause(proof: &ProofElaborated) -> bool {
    match proof.commands.last() {
        Some(ProofCommand::Step(s)) => s.clause.is_empty(),
        _ => false,
    }
}

/// The names that have to carry the hypothesis, computed over the emitted commands
/// rather than over the Alethe premises.
///
/// The two agree, but only the emitted form is what the rewrite below has to match:
/// a rule handler is free to cite a symbol the Alethe step does not list as a
/// premise, and the resolution chains in `rules/core.rs` do. Commands are emitted in
/// dependency order -- a symbol can only mention symbols already declared -- so one
/// forward pass reaches the fixpoint.
fn tainted_by(commands: &[Command], assume_id: &str) -> HashSet<String> {
    let mut tainted: HashSet<String> = HashSet::from([assume_id.to_owned()]);

    for command in commands {
        let Command::Symbol(_, name, _, _, Some(proof)) = command else {
            continue;
        };
        let mut mentioned = HashSet::new();
        collect_proof(proof, &mut mentioned, &mut Scope::new());
        if mentioned.iter().any(|n| tainted.contains(n)) {
            tainted.insert(name.clone());
        }
    }

    tainted
}

/// Give every tainted symbol the hypothesis as a parameter, and pass it at each use.
///
/// Doing this on the finished AST rather than inside the rule handlers is what keeps
/// it tractable: step names are built in dozens of places (`unary_clause_to_prf`, the
/// `disj_resolutionN*` chains, the `have` plumbing in `translate_subproof`), and they
/// all funnel into `Term::TermId` here.
fn thread(
    commands: &mut Vec<Command>,
    tainted: &HashSet<String>,
    assume_id: &str,
    hyp_type: &Term,
) {
    commands.retain(|c| !matches!(c, Command::Symbol(_, name, _, _, None) if name == assume_id));

    for command in commands.iter_mut() {
        let Command::Symbol(_, name, params, _, proof) = command else {
            continue;
        };
        let carries_hyp = tainted.contains(name.as_str());
        if carries_hyp {
            params.push(Param(HYP.to_owned(), hyp_type.clone()));
        }
        if let Some(proof) = proof {
            rewrite_proof(proof, tainted, assume_id, &mut Scope::new());
            if carries_hyp {
                // A symbol's parameters are not introduced into the tactic context on
                // their own -- the goal stays `Π hGoal, …` until the script assumes
                // it (see `case_l` in core.lp, which opens with `assume a x l n`).
                proof.0.insert(0, ProofStep::Assume(vec![HYP.to_owned()]));
            }
        }
    }
}

/// Names bound inside a tactic script, which hide a global of the same name for the
/// rest of their block.
///
/// This is not hypothetical: the resolution chains name their intermediate `have`s
/// after the premises they combine, so a script can contain `have t2_t3 : …` while a
/// top-level `symbol t2_t3` also exists. Rewriting the local one into `t2_t3 hGoal`
/// applies a proof of a clause to an argument, which Lambdapi reports as a confusing
/// conversion failure rather than an arity error.
type Scope = HashSet<String>;

/// Rewrite the *uses*: the discharged assume becomes the bound hypothesis, and a
/// tainted symbol becomes an application of it.
fn rewrite_term(term: &mut Term, tainted: &HashSet<String>, assume_id: &str, scope: &Scope) {
    match term {
        Term::TermId(id) if scope.contains(id.as_str()) => {}
        Term::TermId(id) if id == assume_id => *id = HYP.to_owned(),
        Term::TermId(id) if tainted.contains(id.as_str()) => {
            *term = Term::Terms(vec![
                Term::TermId(std::mem::take(id)),
                Term::TermId(HYP.to_owned()),
            ]);
        }
        Term::TermId(_) | Term::Sort(_) | Term::Nat(_) | Term::Int(_) | Term::Underscore => {}
        Term::Terms(ts) | Term::Function(ts) => {
            ts.iter_mut()
                .for_each(|t| rewrite_term(t, tainted, assume_id, scope));
        }
        Term::Alethe(t) => rewrite_lterm(t, tainted, assume_id, scope),
    }
}

/// A step's own type mentions no proof symbol, but a clause built by a rule handler
/// can carry one inside `π̇ₗ`/`disj` arguments, so the Alethe layer is walked too.
fn rewrite_lterm(term: &mut LTerm, tainted: &HashSet<String>, assume_id: &str, scope: &Scope) {
    let go = |t: &mut Term| rewrite_term(t, tainted, assume_id, scope);
    match term {
        LTerm::True | LTerm::False | LTerm::Neg(None) => {}
        LTerm::Neg(Some(t))
        | LTerm::ClassicProof(t)
        | LTerm::Proof(t)
        | LTerm::Forall(_, t)
        | LTerm::Exist(_, t)
        | LTerm::Choice(_, t) => go(t),
        LTerm::Implies(a, b) | LTerm::Iff(a, b) | LTerm::Eq(a, b) => {
            go(a);
            go(b);
        }
        LTerm::NAnd(ts) | LTerm::NOr(ts) | LTerm::Clauses(ts) => ts.iter_mut().for_each(go),
        LTerm::Distinct(VecN(ts)) | LTerm::List(List(ts)) => ts.iter_mut().for_each(go),
    }
}

fn rewrite_proof(proof: &mut Proof, tainted: &HashSet<String>, assume_id: &str, scope: &mut Scope) {
    rewrite_steps(&mut proof.0, tainted, assume_id, scope);
}

/// Steps are walked in order so a binding takes effect only from the step after it,
/// which is where the shadowing starts. A nested block gets a copy of the scope: what
/// it binds does not escape it.
fn rewrite_steps(
    steps: &mut [ProofStep],
    tainted: &HashSet<String>,
    assume_id: &str,
    scope: &mut Scope,
) {
    for step in steps {
        match step {
            ProofStep::Apply(t, sp) | ProofStep::Refine(t, sp) => {
                rewrite_term(t, tainted, assume_id, scope);
                rewrite_subproofs(sp, tainted, assume_id, scope);
            }
            ProofStep::Rewrite(_, _, t, args, sp) => {
                rewrite_term(t, tainted, assume_id, scope);
                args.iter_mut()
                    .for_each(|a| rewrite_term(a, tainted, assume_id, scope));
                rewrite_subproofs(sp, tainted, assume_id, scope);
            }
            ProofStep::Have(name, t, steps) => {
                rewrite_term(t, tainted, assume_id, scope);
                rewrite_steps(steps, tainted, assume_id, &mut scope.clone());
                scope.insert(name.clone());
            }
            ProofStep::Try(inner) => {
                rewrite_steps(
                    std::slice::from_mut(inner.as_mut()),
                    tainted,
                    assume_id,
                    scope,
                );
            }
            ProofStep::Change(t) | ProofStep::Eval(t) => {
                rewrite_term(t, tainted, assume_id, scope);
            }
            ProofStep::Set(name, t) => {
                rewrite_term(t, tainted, assume_id, scope);
                scope.insert(name.clone());
            }
            ProofStep::Varmap(name, ts) => {
                ts.iter_mut()
                    .for_each(|t| rewrite_term(t, tainted, assume_id, scope));
                scope.insert(name.clone());
            }
            ProofStep::Assume(names) => scope.extend(names.iter().cloned()),
            ProofStep::Admit
            | ProofStep::Reflexivity
            | ProofStep::Symmetry
            | ProofStep::Simplify(_)
            | ProofStep::Why3 => {}
        }
    }
}

fn rewrite_subproofs(
    sp: &mut SubProofs,
    tainted: &HashSet<String>,
    assume_id: &str,
    scope: &Scope,
) {
    if let SubProofs(Some(proofs)) = sp {
        proofs
            .iter_mut()
            .for_each(|p| rewrite_proof(p, tainted, assume_id, &mut scope.clone()));
    }
}

/// Free names a term mentions. Mirrors `rewrite_term`'s shadowing so the two passes
/// agree on which occurrences refer to a global.
fn collect_term(term: &Term, out: &mut HashSet<String>, scope: &Scope) {
    match term {
        Term::TermId(id) => {
            if !scope.contains(id.as_str()) {
                out.insert(id.clone());
            }
        }
        Term::Terms(ts) | Term::Function(ts) => {
            ts.iter().for_each(|t| collect_term(t, out, scope));
        }
        Term::Alethe(t) => collect_lterm(t, out, scope),
        Term::Sort(_) | Term::Nat(_) | Term::Int(_) | Term::Underscore => {}
    }
}

fn collect_lterm(term: &LTerm, out: &mut HashSet<String>, scope: &Scope) {
    match term {
        LTerm::True | LTerm::False | LTerm::Neg(None) => {}
        LTerm::Neg(Some(t))
        | LTerm::ClassicProof(t)
        | LTerm::Proof(t)
        | LTerm::Forall(_, t)
        | LTerm::Exist(_, t)
        | LTerm::Choice(_, t) => collect_term(t, out, scope),
        LTerm::Implies(a, b) | LTerm::Iff(a, b) | LTerm::Eq(a, b) => {
            collect_term(a, out, scope);
            collect_term(b, out, scope);
        }
        LTerm::NAnd(ts) | LTerm::NOr(ts) | LTerm::Clauses(ts) => {
            ts.iter().for_each(|t| collect_term(t, out, scope));
        }
        LTerm::Distinct(VecN(ts)) | LTerm::List(List(ts)) => {
            ts.iter().for_each(|t| collect_term(t, out, scope));
        }
    }
}

fn collect_proof(proof: &Proof, out: &mut HashSet<String>, scope: &mut Scope) {
    collect_steps(&proof.0, out, scope);
}

fn collect_steps(steps: &[ProofStep], out: &mut HashSet<String>, scope: &mut Scope) {
    for step in steps {
        match step {
            ProofStep::Apply(t, sp) | ProofStep::Refine(t, sp) => {
                collect_term(t, out, scope);
                collect_subproofs(sp, out, scope);
            }
            ProofStep::Rewrite(_, _, t, args, sp) => {
                collect_term(t, out, scope);
                args.iter().for_each(|a| collect_term(a, out, scope));
                collect_subproofs(sp, out, scope);
            }
            ProofStep::Have(name, t, steps) => {
                collect_term(t, out, scope);
                collect_steps(steps, out, &mut scope.clone());
                scope.insert(name.clone());
            }
            ProofStep::Try(inner) => {
                collect_steps(std::slice::from_ref(inner.as_ref()), out, scope);
            }
            ProofStep::Change(t) | ProofStep::Eval(t) => collect_term(t, out, scope),
            ProofStep::Set(name, t) => {
                collect_term(t, out, scope);
                scope.insert(name.clone());
            }
            ProofStep::Varmap(name, ts) => {
                ts.iter().for_each(|t| collect_term(t, out, scope));
                scope.insert(name.clone());
            }
            ProofStep::Assume(names) => scope.extend(names.iter().cloned()),
            ProofStep::Admit
            | ProofStep::Reflexivity
            | ProofStep::Symmetry
            | ProofStep::Simplify(_)
            | ProofStep::Why3 => {}
        }
    }
}

fn collect_subproofs(sp: &SubProofs, out: &mut HashSet<String>, scope: &Scope) {
    if let SubProofs(Some(proofs)) = sp {
        proofs
            .iter()
            .for_each(|p| collect_proof(p, out, &mut scope.clone()));
    }
}

/// Rewrite `commands` so the last assertion is discharged, and append the theorem it
/// proves. Returns `false` and leaves `commands` untouched when the proof does not
/// have the shape this needs, in which case the file keeps ending at `π̇ □`.
pub fn discharge(commands: &mut Vec<Command>, proof: &ProofElaborated, ctx: &Context) -> bool {
    if !ends_in_empty_clause(proof) {
        return false;
    }
    let Some((assume_id, assume_term)) = discharged_assume(proof) else {
        return false;
    };
    // The refutation is the last emitted symbol; a rule that reports no script emits
    // nothing, so the last command is not necessarily the last Alethe step.
    let Some(Command::Symbol(_, refutation, ..)) = commands.last() else {
        return false;
    };
    let refutation = refutation.clone();

    // `π̇ (A ⸬ □)`, the type the assume axiom had.
    let hyp_type = term::clauses(vec![ctx.get_or_convert(&assume_term).0]);

    let tainted = tainted_by(commands, &assume_id);
    thread(commands, &tainted, &assume_id, &hyp_type);

    // `refutation` is `π̇ □`, which is `π ⊥`; `clᵢ₁'` lifts the bound hypothesis back
    // into the one-literal clause the steps expect.
    let refutation_applied = if tainted.contains(&refutation) {
        Term::Terms(vec![
            Term::from(refutation),
            Term::Terms(vec![Term::from("clᵢ₁'"), Term::from(HYP)]),
        ])
    } else {
        Term::from(refutation)
    };

    let mut script = vec![];
    let statement = match assume_term.deref() {
        // The last assertion is the negated conjecture, the usual shape: state the
        // conjecture itself. `contradiction p : (π (¬ p) → π ⊥) → π p`.
        AletheTerm::Op(Operator::Not, args) if args.len() == 1 => {
            script.push(ProofStep::Apply(
                Term::from("contradiction"),
                SubProofs(None),
            ));
            ctx.get_or_convert(&args[0]).0
        }
        // Any other assertion: conclude its negation. `¬ a ≔ a ⇒ ⊥` is a definition,
        // so `assume` alone introduces it -- no lemma needed.
        _ => Term::Alethe(LTerm::Neg(Some(Box::new(
            ctx.get_or_convert(&assume_term).0,
        )))),
    };
    script.push(ProofStep::Assume(vec![HYP.to_owned()]));
    script.push(ProofStep::Refine(refutation_applied, SubProofs(None)));

    commands.push(Command::Symbol(
        Some(Modifier::Opaque),
        // The discharged assume's id is free now that its axiom is gone, and it is
        // the name the problem gave the assertion -- `Goal` for anything produced by
        // TLAPS, which names its conjecture `:named |Goal|`.
        assume_id,
        vec![],
        Term::Alethe(LTerm::ClassicProof(Box::new(statement))),
        Some(Proof(script)),
    ));

    true
}
