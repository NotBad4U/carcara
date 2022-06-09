mod deep_eq;
mod diff;
mod pruning;

use crate::{ast::*, utils::SymbolTable};
use deep_eq::DeepEqReconstructor;
use diff::{apply_diff, CommandDiff, ProofDiff};
use pruning::prune_proof;

#[derive(Debug, Default)]
struct Frame {
    diff: Vec<(usize, CommandDiff)>,
    new_indices: Vec<(usize, usize)>,
    current_offset: isize,
    subproof_length: usize,
}

impl Frame {
    fn current_index(&self) -> usize {
        self.new_indices.len()
    }

    fn push_new_index(&mut self, current_depth: usize) -> (usize, usize) {
        let old_index = self.current_index();
        let new_index = (self.current_index() as isize + self.current_offset) as usize;
        self.new_indices.push((current_depth, new_index));
        (old_index, new_index)
    }
}

#[derive(Debug)]
pub struct Reconstructor {
    stack: Vec<Frame>,
    seen_clauses: SymbolTable<Vec<Rc<Term>>, usize>,
    accumulator: Vec<ProofCommand>,
}

impl Default for Reconstructor {
    fn default() -> Self {
        Self::new()
    }
}

impl Reconstructor {
    pub fn new() -> Self {
        Self {
            stack: vec![Frame::default()],
            accumulator: Vec::new(),
            seen_clauses: SymbolTable::new(),
        }
    }

    fn top_frame(&self) -> &Frame {
        self.stack.last().unwrap()
    }

    fn top_frame_mut(&mut self) -> &mut Frame {
        self.stack.last_mut().unwrap()
    }

    fn depth(&self) -> usize {
        self.stack.len() - 1
    }

    /// Returns `true` if the command on the current frame at index `index` cannot be deleted.
    fn must_keep(&self, index: usize) -> bool {
        // If the command is the second to last in a subproof, it may be implicitly used by the last
        // step in the subproof, so we cannot delete it
        if index + 2 == self.top_frame().subproof_length {
            return true;
        }

        // We must also consider the edge case when the step closes a subproof that
        // is itself the second to last command in an outer subproof. If we delete this
        // step, the inner subproof will also be deleted, which will invalidate the implicit
        // reference used in the last step of the outer subproof
        let depth = self.depth();
        if depth >= 2 {
            let outer_frame = &self.stack[depth - 1];
            let index_in_outer = outer_frame.current_index();
            index_in_outer + 2 == outer_frame.subproof_length
        } else {
            false
        }
    }

    /// Maps the index of a command in the original proof to the index of that command in the
    /// reconstructed proof, taking into account the offset created by new steps introduced.
    pub(super) fn map_index(&self, (depth, i): (usize, usize)) -> (usize, usize) {
        self.stack[depth].new_indices[i]
    }

    fn add_new_command(&mut self, command: ProofCommand) -> (usize, usize) {
        if let Some((d, &i)) = self.seen_clauses.get_with_depth(command.clause()) {
            return (d, i);
        }

        let frame = self.top_frame_mut();
        let index = (frame.new_indices.len() as isize + frame.current_offset) as usize;
        frame.current_offset += 1;
        self.seen_clauses.insert(command.clause().to_vec(), index);
        self.accumulator.push(command);
        (self.depth(), index)
    }

    pub(super) fn add_new_step(&mut self, step: ProofStep) -> (usize, usize) {
        self.add_new_command(ProofCommand::Step(step))
    }

    pub(super) fn get_new_id(&mut self, root_id: &str) -> String {
        format!("{}.t{}", root_id, self.accumulator.len() + 1)
    }

    pub(super) fn push_reconstructed_step(&mut self, step: ProofStep) -> (usize, usize) {
        // TODO: discard reconstructed steps that inroduce already seen conclusions (and can be
        // deleted)

        let clause = step.clause.clone();
        let reconstruction = {
            let mut added = std::mem::take(&mut self.accumulator);
            added.push(ProofCommand::Step(step));
            CommandDiff::Step(added)
        };

        let depth = self.depth();
        let frame = self.top_frame_mut();
        let (old_index, new_index) = frame.push_new_index(depth);

        frame.diff.push((old_index, reconstruction));

        self.seen_clauses.insert(clause, new_index);
        (self.depth(), new_index)
    }

    fn push_command(&mut self, clause: &[Rc<Term>], is_assume: bool) {
        let depth = self.depth();
        let frame = self.top_frame_mut();
        let (old_index, new_index) = frame.push_new_index(depth);

        if let Some((depth, &index)) = self.seen_clauses.get_with_depth(clause) {
            let must_keep = self.must_keep(old_index) || is_assume && depth > 0;
            if !must_keep {
                let frame = self.top_frame_mut();
                frame.new_indices[old_index] = (depth, index);
                frame.diff.push((old_index, CommandDiff::Delete));
                frame.current_offset -= 1;
            }
        } else {
            self.seen_clauses.insert(clause.to_vec(), new_index);
        }
    }

    pub(super) fn assume(&mut self, term: &Rc<Term>) {
        self.push_command(std::slice::from_ref(term), true);
    }

    pub(super) fn unchanged(&mut self, clause: &[Rc<Term>]) {
        self.push_command(clause, false);
    }

    /// Adds a `symm` step that flips the equality of the given premise. The `original_premise`
    /// index must already be mapped to the new index space.
    pub(super) fn add_symm_step(
        &mut self,
        pool: &mut TermPool,
        original_premise: (usize, usize),
        original_equality: (Rc<Term>, Rc<Term>),
        id: String,
    ) -> (usize, usize) {
        let (a, b) = original_equality;
        let clause = vec![build_term!(pool, (= {b} {a}))];
        let step = ProofStep {
            id,
            clause,
            rule: "symm".into(),
            premises: vec![original_premise],
            args: Vec::new(),
            discharge: Vec::new(),
        };
        self.add_new_step(step)
    }

    /// Adds a `refl` step that asserts that the given term is equal to itself.
    pub(super) fn add_refl_step(
        &mut self,
        pool: &mut TermPool,
        term: Rc<Term>,
        id: String,
    ) -> (usize, usize) {
        let clause = vec![build_term!(pool, (= {term.clone()} {term}))];
        let step = ProofStep {
            id,
            clause,
            rule: "refl".into(),
            premises: Vec::new(),
            args: Vec::new(),
            discharge: Vec::new(),
        };
        self.add_new_step(step)
    }

    #[allow(dead_code)]
    pub(super) fn reconstruct_assume(
        &mut self,
        pool: &mut TermPool,
        premise: Rc<Term>,
        term: Rc<Term>,
        id: &str,
    ) -> (usize, usize) {
        let new_assume = self.add_new_command(ProofCommand::Assume {
            id: id.to_owned(),
            term: premise.clone(),
        });
        let equality_step = {
            let mut r = DeepEqReconstructor::new(self, id);
            r.reconstruct(pool, premise.clone(), term.clone())
        };
        let equiv1_step = {
            let new_id = self.get_new_id(id);
            let clause = vec![build_term!(pool, (not { premise })), term.clone()];
            self.add_new_step(ProofStep {
                id: new_id,
                clause,
                rule: "equiv1".to_owned(),
                premises: vec![equality_step],
                args: Vec::new(),
                discharge: Vec::new(),
            })
        };

        let new_id = self.get_new_id(id);
        self.push_reconstructed_step(ProofStep {
            id: new_id,
            clause: vec![term],
            rule: "resolution".to_owned(),
            premises: vec![new_assume, equiv1_step],
            args: Vec::new(), // TODO: Add args
            discharge: Vec::new(),
        })
    }

    pub(super) fn open_subproof(&mut self, length: usize) {
        self.seen_clauses.push_scope();
        self.stack.push(Frame {
            diff: Vec::new(),
            new_indices: Vec::new(),
            current_offset: 0,
            subproof_length: length,
        });
    }

    pub(super) fn close_subproof(&mut self) {
        self.seen_clauses.pop_scope();
        let inner = self.stack.pop().expect("can't close root subproof");

        let depth = self.depth();
        let frame = self.top_frame_mut();
        let (old_index, _) = frame.push_new_index(depth);

        let last_command_index = inner.current_index() - 1;
        let diff = if inner.diff.last() == Some(&(last_command_index, CommandDiff::Delete)) {
            CommandDiff::Delete
        } else {
            // Even if the subproof diff is empty, we still need to update the indices of the
            // premises of steps inside the subproof, so we push a `CommandDiff` anyway
            CommandDiff::Subproof(ProofDiff {
                commands: inner.diff,
                new_indices: inner.new_indices,
            })
        };
        frame.diff.push((old_index, diff));
    }

    pub(super) fn end(&mut self, original: Vec<ProofCommand>) -> Vec<ProofCommand> {
        assert!(
            self.depth() == 0,
            "trying to end proof building before closing subproof"
        );
        let Frame { diff, new_indices, .. } = self.stack.pop().unwrap();
        let diff = ProofDiff { commands: diff, new_indices };
        let reconstructed = apply_diff(diff, original);
        apply_diff(prune_proof(&reconstructed), reconstructed)
    }
}
