# The Alethe library for Lambdapi

Lambdapi package `alethe`, so its modules are addressed as `alethe.core`,
`alethe.prop`, and so on. (The package file must be called `lambdapi.pkg` —
that filename is how the tool discovers a package; only its contents name this
one.)

The package holds the lemmas that carcara's Lambdapi backend cites when it
translates an Alethe proof, and it is organised so that a generated proof
imports only what its logic needs.

Build with `make`; install with `make install`. Each module is checked in its
own `lambdapi` process — checking every file in one process trips the `.lpo`
loader on modules carrying string literals.

## Modules

One module per SMT-LIB logic **feature**, not per logic. The standard's 25
logic names are not closed under the feature combinations that occur (there is
no `UF`, no `UFLIA`, no `AUFLRA`, no `LIRA`), so a logic-named module would
either have no logic to belong to or would have to be shared by logics whose
names do not mention it.

| Module | Opened when | Contents |
|---|---|---|
| `core.lp` | always | The Alethe calculus: the `Set`/`τ`/`Prop` bridge, clauses (the stdlib `𝕃 o`, read back as a disjunction by `disj`) and their proof judgement `π̇ l ≔ π (disj l)`, the classical axioms, the propositional lemma toolbox, `ite`, resolution and contraction, equality and congruence (`feq`…`feq8`), the subproof context, and the tactic layer. |
| `prop.lp` | always | Alethe rules whose conclusion is a propositional tautology or a Boolean rewrite, and the Boolean half of the `*_simplify` family. |
| `quant.lp` | quantifiers | Hilbert choice, `forall_inst`, `bind_∀`/`bind_∃`, `sko_forall`. Keeping it separate keeps the choice axiom out of quantifier-free proofs. |
| `lia.lp` | integer arithmetic | The ℤ reification behind `la_generic`, the ℤ ordering lemmas, the `la_*` rules, and the ℤ numeral binding. |
| `lra.lp` | real arithmetic | The ℚ counterpart, on top of `Rat.lp`. Not reachable from the translator yet — the backend has no `Real` sort. |
| `Rat.lp` | support | ℚ as reduced fractions. No Alethe rule dispatches to it, so it has no Rust counterpart. |
| `rare/prop.lp` | with `prop` | The cvc5 RARE rewrites over Booleans and equality: `bool-*` (including `xor`), `ite-*`, `eq-refl`, `eq-symm`, `distinct-binary-elim`, and the `bool_eval` tactic their case-analysis proofs share. |
| `rare/lia.lp` | with `lia` | The cvc5 RARE `arith-*` rewrites over ℤ. |
| `rare/lra.lp` | with `lra` | The `arith-*` rewrites over ℚ. Empty until the backend has a `Real` sort. |

Each module mirrors a Rust module under `src/translation/lambdapi/rules/`, and
every Alethe rule is dispatched to exactly one of them. `rare/` mirrors
`rules/rare/`, whose `RARE_RULES` registry maps every RARE rule name the backend
proves to its lemma or script; a `rare_rewrite` step naming any other rule is
unsupported.

### Where a new rule goes

**The module is the smallest feature the rule's conclusion needs.** Clause-shaped
and proof-structural rules go to `core`; a conclusion that is a propositional
tautology or a Boolean-connective rewrite goes to `prop`; a rule that binds or
instantiates a variable goes to `quant`; a rule over `≤ < + × ÷` goes to `lia`
or `lra` by carrier.

Note that `*_simplify` is a proof *pattern*, not a theory: its members belong to
different modules (`and_simplify` to `prop`, `sum_simplify` to `lia`,
`qnt_simplify` to `quant`, `eq_simplify` to `core`).

**A cvc5 RARE rewrite goes to `rare/`**, in the companion of the smallest module
its statement needs, under the RARE rule's exact name. Register it in `RARE_RULES`
too: a test fails for a registered lemma the library does not declare, and for a
RARE lemma in `rare/` that no entry reaches.

- A `define-cond-rule` lemma takes its conditions as hypotheses after its variables;
  the translator applies it to the step's arguments, then to its premises.
- cvc5 emits a `define-rule*` one unfolding per step. State the one-step lemma, and
  let the script repeat it (`#repeat #rewrite`) on both sides of the equation: a
  single rewrite rule that is orthogonal and terminating brings both to the same
  normal form.
- A rule over `:list` arguments usually cannot be a lemma, because a list does not
  print as a term. Its script works from the list lengths instead, as
  `bool-and-conf` and `bool-or-taut` do.

## Logic → modules

The translator opens the theory modules the declared `(set-logic …)` needs, whether
or not the proof's steps use them, and widens that with anything the steps use
beyond it (with a warning, since it usually means the declaration is wrong). Each
`rare/` module is opened with its theory module, whether or not a step cites one of
its lemmas; gating them on the `rare_rewrite` steps is a planned refinement. Of the
25 standard logics, 11 are fully in scope and 4 more translate as far as their
proofs stay linear:

| Logic | Header (`rare.X` is `alethe.rare.X`) |
|---|---|
| `QF_UF` | `core prop rare.prop` |
| `QF_LIA`, `QF_IDL`, `QF_UFLIA`, `QF_UFIDL` | `core prop rare.prop lia rare.lia` |
| `QF_LRA`, `QF_RDL`, `QF_UFLRA` | `core prop rare.prop lra rare.lra` |
| `LIA` | `core prop rare.prop quant lia rare.lia` |
| `LRA`, `UFLRA` | `core prop rare.prop quant lra rare.lra` |
| `QF_NIA`, `QF_NRA`, `QF_UFNRA`, `UFNIA` | as above; genuinely non-linear steps are unsupported |
| `AUFLIA`, `AUFLIRA`, `AUFNIRA`, `QF_AUFLIA`, `QF_AX` | unsupported: arrays |
| `QF_BV`, `QF_UFBV`, `QF_ABV`, `QF_AUFBV` | unsupported: bit-vectors |
| `QF_EIA` | unsupported: exponentiation |
| `ALL`, none, or a name the standard does not list (`UF`, `UFLIA`) | `core prop rare.prop`, plus what the steps use |

**An unrecognised logic opens nothing by itself.** Solvers accept names the standard
does not list, and `ALL` promises every theory. Opening everything for them would open
`lia` and `lra` together, and put the ℤ layer's admits and the Hilbert choice axioms
into proofs that use neither, so their header is exactly what the steps use. For the
same reason `AUFLIRA` and `AUFNIRA`, which declare both carriers, open neither by
themselves, and a proof whose steps use both is rejected.

**Numerals in a generated proof are qualified.** Decimal notation can be bound to
only one type at a time (Deducteam/lambdapi#1268), and the binding belongs to
whatever the file required last, so a bare `3` would mean ℕ in a proof whose header
stops at `core` and ℤ in one that also opens `lia`. The translator therefore emits
every literal as `Stdlib.Nat.n` or `Stdlib.Z.n`: `Module.n` is one token, scoped
against that module's own `builtin "0".."10"` table, so it denotes the same thing
whatever the ambient notation is. Because the module tables carry `+` and `*` too,
there is no ceiling — `Stdlib.Nat.42` is written directly.

That replaced `int2nat`, which existed only to undo `lia`'s own rebinding and so had
to be in scope always — which is why `lia` used to be unconditional. Both it and its
helper `pos2nat` are gone.

A numeral is not free of the header, only of its *order*: `Stdlib.Z.n` and the `int`
sort name both come from `Stdlib.Z`, which a generated proof reaches only through
`lia`, so an integer literal or an Int-sorted declaration puts `lia` in the header
just as a `la_*` step does.

**The order still matters inside this library.** These modules write bare numerals,
so the last arithmetic module opened decides what they mean: `core` binds numerals to
ℕ and `lia` rebinds them to ℤ, which is why `lia.lp` re-pins them after opening
`core` mid-file, and `rare/lia.lp` after its own requires. `lia` and `lra` must not be opened together — they declare the same
reification machinery (`G`, `Cst`, `Var`, `rec_G`, `reify`).

## Known debt

These modules are not fully proved. A proof that opens them inherits the gap.

| Module | `admit`s | Axioms |
|---|---|---|
| `core.lp` | 1 (`disj_resolutionN2`) | 5 |
| `prop.lp` | 0 | 1 |
| `quant.lp` | 0 | 2 (Hilbert choice: `ϵᵢ`, `ϵ_det`) |
| `lia.lp` | 6 | 11 |
| `lra.lp` | 2 | 3 |
| `Rat.lp` | 15 | 1 |
| `rare/prop.lp` | 0 | 0 |
| `rare/lia.lp` | 2 (`arith-geq-tighten`, `arith-leq-norm`) | 0 |
| `rare/lra.lp` | 0 | 0 |

Several axioms (`rec_ℕ`, `list_ind2_principle`, `rec_G`, `eta_prod`) are
derivable and are axioms only for convenience; `lia.lp` also carried `ind_ℤ`,
`ind_ℤ₂` and `ind_ℙ`, which nothing used, and they are gone.
`nnpp_eq`, `prop_ext` and the choice axioms are deliberate. `core.lp` used to
carry two more, `ind_ℂ` and `Clause_ind`: clauses had their own type, which was
not declared `inductive`, so its induction principles had to be postulated.
Clauses are now the stdlib `𝕃 o` and both come from `ind_𝕃`. `Rat.lp` is the
weakest link: 15 of the 17 lemmas in its neutral-element section are admitted,
so anything built on `lra.lp` checks only because of them.
