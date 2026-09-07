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
| `prop.lp` | always | Alethe rules whose conclusion is a propositional tautology or a Boolean rewrite, the Boolean half of the `*_simplify` family, and the cvc5 RARE `bool-*` rewrites. |
| `quant.lp` | logic is not quantifier-free | Hilbert choice, `forall_inst`, `bind_∀`/`bind_∃`, `sko_forall`. Keeping it separate keeps the choice axiom out of quantifier-free proofs. |
| `lia.lp` | integer arithmetic | The ℤ reification behind `la_generic`, the ℤ ordering lemmas, the `arith-*` RARE rewrites, and the ℤ numeral binding. |
| `lra.lp` | real arithmetic | The ℚ counterpart, on top of `Rat.lp`. Not reachable from the translator yet — the backend has no `Real` sort. |
| `Rat.lp` | support | ℚ as reduced fractions. No Alethe rule dispatches to it, so it has no Rust counterpart. |

Each module mirrors a Rust module under `src/translation/lambdapi/rules/`, and
every Alethe rule is dispatched to exactly one of them.

### Where a new rule goes

**The module is the smallest feature the rule's conclusion needs.** Clause-shaped
and proof-structural rules go to `core`; a conclusion that is a propositional
tautology or a Boolean-connective rewrite goes to `prop`; a rule that binds or
instantiates a variable goes to `quant`; a rule over `≤ < + × ÷` goes to `lia`
or `lra` by carrier.

Note that `*_simplify` is a proof *pattern*, not a theory: its members belong to
different modules (`and_simplify` to `prop`, `sum_simplify` to `lia`,
`qnt_simplify` to `quant`, `eq_simplify` to `core`).

## Logic → modules

The translator derives the `require open` header from `(set-logic …)`, widened
by the features the proof's steps actually use. Of the 25 standard logics, 11
are fully in scope and 4 more translate as far as their proofs stay linear:

| Logic | Header |
|---|---|
| `QF_UF` | `core prop` * |
| `QF_LIA`, `QF_IDL`, `QF_UFLIA`, `QF_UFIDL` | `core prop lia` |
| `QF_LRA`, `QF_RDL`, `QF_UFLRA` | `core prop lra` |
| `LIA` | `core prop quant lia` |
| `LRA`, `UFLRA` | `core prop quant lra` |
| `QF_NIA`, `QF_NRA`, `QF_UFNRA`, `UFNIA` | as above; genuinely non-linear steps are unsupported |
| `AUFLIA`, `AUFLIRA`, `AUFNIRA`, `QF_AUFLIA`, `QF_AX` | unsupported: arrays |
| `QF_BV`, `QF_UFBV`, `QF_ABV`, `QF_AUFBV` | unsupported: bit-vectors |
| `QF_EIA` | unsupported: exponentiation |

\* `lia.lp` is currently opened unconditionally, because the n-ary clause rules
take their ℕ indices through `int2nat`, which lives there. See "Known debt".

**The order matters.** Decimal notation can be bound to only one type at a time
(Deducteam/lambdapi#1268), so the last arithmetic module opened decides what a
numeral means. `core` binds numerals to ℕ for the clause indices; `lia` and
`lra` rebind them to their own carrier and are opened after it. For the same
reason `lra` is opened only when a proof really produced real arithmetic, never
merely because an unrecognised logic declared every feature — `lia` and `lra`
must not be opened together.

## Known debt

These modules are not fully proved. A proof that opens them inherits the gap.

| Module | `admit`s | Axioms |
|---|---|---|
| `core.lp` | 1 (`disj_resolutionN2`) | 5 |
| `prop.lp` | 0 | 1 |
| `quant.lp` | 0 | 2 (Hilbert choice: `ϵᵢ`, `ϵ_det`) |
| `lia.lp` | 8 | 14 |
| `lra.lp` | 2 | 3 |
| `Rat.lp` | 15 | 1 |

Several axioms (`rec_ℕ`, `list_ind2_principle`, `ind_ℤ`, `rec_G`, `eta_prod`) are
derivable and are axioms only for convenience;
`nnpp_eq`, `prop_ext` and the choice axioms are deliberate. `core.lp` used to
carry two more, `ind_ℂ` and `Clause_ind`: clauses had their own type, which was
not declared `inductive`, so its induction principles had to be postulated.
Clauses are now the stdlib `𝕃 o` and both come from `ind_𝕃`. `Rat.lp` is the
weakest link: 15 of the 17 lemmas in its neutral-element section are admitted,
so anything built on `lra.lp` checks only because of them.
