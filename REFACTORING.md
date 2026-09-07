# Lambdapi backend: a theory-oriented module architecture

## Context

An earlier draft of this document proposed a 16-module, fragment-oriented split (`core`,
`tactic`, `listsort`, `clause`, `prop`, `equality`, `quantifiers`, `simplify`, `rare`, `la`,
`lia`, `lra`, `rat`, `zgcd`, `rare_arith`, `bv`). That granularity is finer than the goal it was
meant to serve.

The goal is: read `(set-logic …)`, decide which Lambdapi modules the proof needs, import only
those. This document revises the architecture around that goal — coarse modules that correspond
to SMT-LIB theory features, with a 1:1 Rust mirror.

**Why this is worth doing at all — it is not tidiness.** Which modules a generated proof opens
decides what `0`, `+` and `*` *mean* in it. `builtin "0"` is rebound in
[Alethe.lp:9-19](alethe-lp/Alethe.lp#L9-L19) (→ℕ, plus `builtin "+" ≔ Stdlib.Nat.+` at
:20-21) and in [Rare.lp:225-235](alethe-lp/Rare.lp#L225-L235) (→ℤ, with the comment *"the
last one loaded wins"*), and upstream in `Stdlib.{Nat,Z,Pos,MergeSort,BitVector}`. Today
[mod.rs:143-151](src/translation/lambdapi/mod.rs#L143-L151) emits the same five `require open`s
for every proof regardless of logic, so numeral meaning is decided by accidental require order.
There is already a live bug from this: `Rare.lp` re-pins `"0".."10"` to ℤ but *not* `"+"`/`"*"`,
and it loads `Stdlib.Pos` last (:221), so inside `Rare.lp` and everything inheriting from it the
numerals are ℤ while `+`/`*` are ℙ.

## Decisions

| Question | Decision |
|---|---|
| Always-on / quantifier layer names | `core.lp` + `prop.lp` + `quant.lp` (not `qf.lp`/`uf.lp`) |
| Arithmetic | `la.lp` (carrier-generic) + `lia.lp` (ℤ) + `lra.lp` (ℚ) |
| Import source | `set-logic` drives the header; observed features cross-check and warn |
| Stdlib rebase | Yes for `Stdlib.Zgcd` and `Stdlib.NaryFun`; **no** for `Stdlib.MergeSort` (keep the local mergesort) |

## Design principle

**One module per SMT-LIB logic *feature*, not per logic and not per proof-engineering fragment.**

SMT-LIB logic names are compositions of feature codes (`QF_`, `A`, `UF`, `BV`, `LIA`, `LRA`, …),
and the features compose by union — which is exactly the shape of an import list. The *names*,
however, do not: the standard defines exactly 25 logics
([smt-lib.org/logics.shtml](https://smt-lib.org/logics.shtml)) and that set is **not closed under
the feature combinations that actually occur**. There is no `UF`, no `UFLIA`, no `AUFLRA`, no
`LIRA` and no `QF_LIRA`. So modules cannot be named after logics even in principle — a
logic-named file either has no logic to belong to, or has to be shared by logics whose names do
not contain it. Naming them after *features* is the only decomposition that closes.

Two further consequences:

- `qf.lp` is rejected because *propositional reasoning is not quantifier-free-specific*: the tlaps
  corpus is quantified and uses `equiv_pos2` 1234×, `or` 746×, `and_pos` 656×, `equiv_simplify`
  449×. A file named `qf` that every quantified proof must open is a name that misleads.
- `uf.lp` is rejected because in SMT-LIB *UF means uninterpreted functions*, which `QF_UF`
  already has, and because **UF needs no module of its own**: uninterpreted symbols are served by
  `core`'s congruence plus the `declare-fun` emission in `translate_prelude`
  ([mod.rs:117-140](src/translation/lambdapi/mod.rs#L117-L140)). The layer that would be called
  `uf.lp` is really the quantifier layer, and `LIA`/`LRA`/`QF_NRA` need it or not independently
  of UF. (There is also no logic named `UF` to open it — see above.)

Placement rule for a new Alethe rule: **the module is the smallest feature its conclusion needs.**
Clause-shaped and proof-structural rules go to `core`; rules whose conclusion is a propositional
tautology or a Boolean-connective rewrite go to `prop`; rules that bind or instantiate a variable
go to `quant`; rules over `≤ < + × ÷` go to `la`, with ℤ- or ℚ-only facts in `lia`/`lra`.

**Transitive `open` works** (`doc/commands.rst:259`: *"Non-private `open` commands are
transitively inherited"*). The earlier draft's "Lambdapi has no re-export" risk note is wrong for
lambdapi 3.0, and the library already depends on the transitivity: generated proofs call
`#repeat_or_id_r` from `Tactic.lp`, which is opened only via `Simplify.lp:2`. So `prop.lp` can
`require open alethe.core` and the header need only name the maximal layers.

## 1. `alethe-lp/` layout

```
core.lp    always. The Alethe calculus and everything unconditional:
           Set/τ/Prop bridge, clause type (▩ ⟇ ++ π̇ π̇ₗ ⟇ᵢ ⟇ₑ) and the ∨↔⟇ bridge,
           classical axioms (nnpp_eq, prop_ext, ⟺_ext), the propositional lemma
           toolbox (morgan, distributive, idempotent, imp_eq_or, contrapos), ite,
           resolutionₗ/ᵣ + disj_resolutionN1/2, list-clause machinery (literal,
           disj/conj + correctness, select, cl↪list, orN_*, eraseIdx, case_l,
           sym_clause), the local mergesort + reification-index helper, contraction,
           equality & congruence (feq..feq8, cong_or/and/imp, ite_cong, distinct),
           subproof/context, let, the connective builtins, the tactic layer,
           int2nat/pos2nat.
prop.lp    always. Alethe rules whose conclusion is propositional: true/false,
           and/or/not_and/not_or, and_pos/neg, or_pos/neg, xor*, implies*, equiv*,
           ite1/2, ite_pos/neg, not_ite*, connective_def, bfun_elim, ite_intro,
           and_intro, ∧ₑₙ/∨ₑₙ, morganN2; Boolean simplification (and/or/not/
           implies/equiv/bool/ite_simplify, ac_simp, aci_simp, nary_elim, shuffle);
           Boolean cvc5 RARE rules (bool-*, eq-refl, eq-symm, ite-eq).
quant.lp   iff the logic is not QF. Choice (ε, from Stdlib.Epsilon), forall_inst,
           bind_∀/∃, sko_forall, sko_ex, qnt_cnf, qnt_simplify, onepoint, qnt_join,
           qnt_rm_unused, miniscope_*.
la.lp      iff any arithmetic. Carrier-generic: the LinOrd ordered-ring signature,
           Farkas machinery (la_generic steps 1,2,3,5), reification/normalisation,
           la_disequality, la_totality, la_tautology, la_mult_pos/neg, la_rw_eq, and
           the *statements* of sum/prod/minus/unary_minus/comp/div_simplify.
lia.lp     iff Int. ℤ instance of LinOrd, ℤ numeral binding, integer strengthening
           (Zgt_le_succ_r_eq — step 4 of la_generic), lia_generic, div/mod folding,
           the ℤ-only arith-* RARE rules.
lra.lp     iff Real. ℚ instance, ℚ numeral binding, real division folding, built on
           Rat.lp.
Rat.lp     support (no Rust counterpart): ℚ as reduced fractions, retargeted to
           Stdlib.Zgcd.
```

Deleted: `Lia.lpi` (622 lines, never compiled — `Makefile:1` is `wildcard *.lp`), `LiaAC.lp` (249,
no in-edges, 87 of them a block comment), `Naryfun.lp` (→ `Stdlib.NaryFun`), `Zgcd.lp` (→
`Stdlib.Zgcd`), `Alethe.lp`/`Clause.lp`/`Simplify.lp`/`Rare.lp`/`Lia.lp`/`La.lp` (split), and
`Tactic.lp` (folded into `core.lp`; keep it as a support file if the `builtin "String"`
one-process-per-module constraint documented in `Makefile:6-8` bites).

**7 files instead of 12** (16 in the fragment proposal), of which two are support files with no
Rust counterpart. Rough sizes: `core.lp` ≈ 1600, `prop.lp` ≈ 1600, `quant.lp` ≈ 260, `la.lp` ≈
600, `lia.lp` ≈ 360. Total ≈ 4400 against today's 7027.

### Why `core + clause + equality` is one module

- **None of it is ever conditional.** The tlaps corpus uses `resolution` 4463×, `cong` 1864×,
  `trans` 1025×, `reordering` 947×, `contraction` 640×, `refl` 462×. There is no logic in which
  the clause calculus or congruence is optional, and a boundary that never changes the import set
  is a file boundary, not a module boundary.
- **They are entangled.** `eq_congruent` has a clause conclusion, `contraction` needs the sort
  infrastructure, `cong` is what every theory routes equalities through. Separate `.lp` files
  would need mutual `require`s.
- **Cost:** `core.lp` ≈ 1600 lines. Still well under `Alethe.lp`'s 2769. If it grows, split it
  into private helper files that `core.lp` re-exports — transitive `open` keeps the *import unit*
  coarse while the files stay small.

One refinement: the **propositional lemma toolbox** (`morgan1/2`, `distributive_*`,
`*_idempotent`, `imp_eq_or`, `contrapos` —
[Alethe.lp:221-414](alethe-lp/Alethe.lp#L221-L414)) goes in `core.lp`, not `prop.lp`. It is
classical-logic infrastructure that `core`'s own resolution and clause proofs use; putting it in
`prop.lp` would make `core` require `prop` and close a cycle. `prop.lp` holds the Alethe *rules*,
`core.lp` the logic they are proved from.

### Why propositional + simplification share `prop.lp` — with one correction

Yes for the Boolean part: `and/or/not/implies/equiv/bool/ite_simplify`, `ac_simp`, `aci_simp` are
Boolean-connective rewrites proved by the same `eval`/`#rewrite` driver and the same lemma toolbox
as clausification. Boolean RARE rewrites belong with them — [Rare.lp:47](alethe-lp/Rare.lp#L47)
already defines `bool-double-not-elim ≔ not_simplify1 t`, i.e. the two families are already
aliases of each other in eight places.

**But `*_simplify` is a proof pattern, not a theory, and must stop being treated as one.** Its
members split by theory: `sum/prod/minus/unary_minus/comp/div_simplify` → arithmetic,
`qnt_simplify` → quantifiers, `eq_simplify` → core, `mod_simplify` → lia. Today's
`rule.contains("simp")` guard at [mod.rs:741](src/translation/lambdapi/mod.rs#L741) treats them as
one family and routes the rest into `unimplemented!` at
[simp.rs:417](src/translation/lambdapi/simp.rs#L417) — 13 real rules panic the translator. The
guard must be deleted; the coarse scheme makes the correct split explicit rather than hiding it.

### `quant.lp`: the quantifier rules, minus `let`

- **`let` and `bind_let` do not belong there.** `(let …)` is quantifier-free and cvc5 emits
  `let`/`bind_let` in QF proofs. They are context/binder rules and go to `core.lp`, next to the
  subproof-context machinery they share ([mod.rs:456](src/translation/lambdapi/mod.rs#L456),
  `VisitorArgs` at [term.rs:271](src/translation/lambdapi/term.rs#L271)).
- **`quant.lp` is where quantifier *rules* are proved, not where ∀/∃ are defined** — those come
  from `Stdlib.HOL`/`Stdlib.FOL`. So `prop.lp` can state `connective_def` and `bfun_elim` (whose
  statements mention ∀/∃) without requiring `quant.lp`.

Bonus: choice/ε moves to `quant.lp` and comes from `Stdlib.Epsilon` instead of the local axioms at
[Alethe.lp:418-419](alethe-lp/Alethe.lp#L418-L419). A QF proof then never imports the choice
axiom — **the module boundaries double as an axiom-footprint statement**, which matters here
because the library carries 8 reachable `admit`s and ~40 convenience axioms.

### Arithmetic: `la` + `lia` + `lra`

`La.lp` is a straight ℚ clone of `Lia.lp` — **38 of its 39 declared symbols also exist in
`Lia.lp`**, block for block (`La.lp:5-522` ≡ `Lia.lp:16-535` with ℤ→ℚ). Sixteen of those
(`mergesort`, `merge`, `split`, `size_split`, `rec_𝕃`, `list_ind2_principle`, `case_l`, `index`,
`compN`, …) are additionally triplicated in `Clause.lp`. So:

- The mergesort + reification-index infrastructure goes to `core.lp` **once** (kept local, not
  rebased on `Stdlib.MergeSort`) and is used by both clause contraction and arithmetic
  reification. That removes two of three copies immediately.
- `la.lp` is parameterised by a `LinOrd` ordered-ring signature; `lia.lp` provides `ℤ_lin`,
  `lra.lp` provides `ℚ_lin`. **Fallback** if the record encoding proves heavy in Lambdapi: keep
  two carrier files with identical lemma names modulo a `Z`/`Q` prefix and share only on the Rust
  side — `la.rs` picks the prefix from the sort. Either way the Rust handler is written once.
- Numeral binding lives **only** in `lia.lp` and `lra.lp`, nowhere else. This is the invariant
  that makes literal meaning deterministic.

**LRA is new work, not a file move.** `BuiltinSort` has no `Real`
([term.rs:42-48](src/translation/lambdapi/term.rs#L42-L48)), `translate_sort_function` hits
`unreachable!` on `Sort::Real` ([mod.rs:107](src/translation/lambdapi/mod.rs#L107)),
`From<&Sort> for Term` hits `todo!` ([term.rs:550](src/translation/lambdapi/term.rs#L550)), and
[lia.rs:355,371,391](src/translation/lambdapi/lia.rs#L355) truncate `Constant::Real` to its
numerator. `lra.lp`/`lra.rs` is therefore staged last.

## 2. `src/translation/lambdapi/` layout

```
mod.rs        produce_lambdapi_proof, Config, Context, the command loop.
              No rule knowledge: calls rules::translate_step.
logic.rs      NEW. Features, features_of_logic(&str), modules(Features).
              The one place that knows the logic→module map. No .lp counterpart.
syntax/       pure move, no logic changes
  term.rs     Term/LTerm/Command/Sort conversion, sharing Visitor
  proof.rs    Proof/ProofStep
  dsl.rs      lambdapi!{} macro
  printer.rs  PrettyPrint
  output.rs   ProofFile/AxiomsFile
rules/
  mod.rs      ONE flat dispatch table translate_step(rule, ctx, step)
              -> TradResult<(Proof, Features)>; TranslatorError::UnsupportedRule;
              shared helpers (unary_clause_to_prf, get_premises_clause, admit)
  core.rs     ↔ core.lp    ~790 lines
  prop.rs     ↔ prop.lp    ~830
  quant.rs    ↔ quant.lp   ~120
  la.rs       ↔ la.lp      ~450
  lia.rs      ↔ lia.lp     ~150
  lra.rs      ↔ lra.lp     (new)
```

The mirror is 1:1 for every module a rule can be dispatched to. Two deliberate exceptions, stated
as a rule so they do not become precedent:

- **A support `.lp` with no Rust module** (`Rat.lp`, and `tactic.lp` if kept): no Alethe rule
  dispatches to it.
- **`logic.rs` with no `.lp`**: it decides the import set.

If `core.rs` outgrows one file, use a `core/` directory with private submodules — the module
*path* `rules::core` is unchanged, so the mirror survives.

Source moves: [tautology.rs](src/translation/lambdapi/tautology.rs) (1269) → `core.rs` (trans,
refl, symm, not_symm, cong+helpers, contraction) / `prop.rs` (the rest) / `quant.rs` (forall_inst,
sko_forall); [mod.rs:204-426,559-626](src/translation/lambdapi/mod.rs#L204-L426) (resolution) and
`translate_subproof` (:456) → `core.rs`; [simp.rs](src/translation/lambdapi/simp.rs) → `prop.rs`
(bool) / `la.rs` (arith); [lia.rs](src/translation/lambdapi/lia.rs) → `la.rs` + `lia.rs`.

## 3. `(set-logic …)` → modules

```rust
// src/translation/lambdapi/logic.rs
bitflags! { pub struct Features: u16 {
    const QUANT; const INT; const REAL; const BV; const ARRAY;
    const STRING; const DT; const FP; const NONLINEAR;
} }
pub fn features_of_logic(logic: Option<&str>) -> Features;
pub fn modules(f: Features) -> Vec<&'static str>;   // topologically ordered
```

Parsing is an **exhaustive table of the 25 standard logic names**, not a greedy scan over feature
codes — the standard's names are irregular (`QF_AX`, `QF_EIA`, `QF_UFIDL`, `AUFNIRA`) and there
are only 25 of them, so a table is both simpler and directly testable. A permissive fallback
covers what solvers accept but the standard does not list — `ALL` (which carcara itself emits as
the default when `logic` is `None`, [printer.rs:702](src/ast/printer.rs#L702)), `HORN`, and
non-standard names such as `UFLIA`: those yield all features plus a warning. Precedent for
logic-string inspection already exists at
[parser/mod.rs:1097-1099](src/parser/mod.rs#L1097-L1099) (`is_real_only_logic`).

| Feature | modules added |
|---|---|
| *(always)* | `core`, `prop` |
| `QUANT` | `quant` |
| `INT` | `la`, `lia` |
| `REAL` | `la`, `lra` |
| `UF` | *(none — served by `core` congruence + `translate_prelude`)* |
| `NONLINEAR` | *(none beyond its base `INT`/`REAL`; nonlinear rules → `UnsupportedRule`)* |
| `ARRAY`, `BV`, `EXP` | *(none — every rule returns `UnsupportedRule`)* |

The full 25-name mapping. **11 logics are fully in scope**, 4 more translate as far as their
proofs stay linear, and 10 are blocked on arrays, bit-vectors or exponentiation:

| Logic | header | |
|---|---|---|
| `QF_UF` | `core prop` | |
| `QF_LIA`, `QF_IDL`, `QF_UFLIA`, `QF_UFIDL` | `core prop la lia` | |
| `QF_LRA`, `QF_RDL`, `QF_UFLRA` | `core prop la lra` | |
| `LIA` | `core prop quant la lia` | |
| `LRA`, `UFLRA` | `core prop quant la lra` | |
| `QF_NIA` | `core prop la lia` | partial — nonlinear steps unsupported |
| `QF_NRA`, `QF_UFNRA` | `core prop la lra` | partial |
| `UFNIA` | `core prop quant la lia` | partial |
| `AUFLIA`, `QF_AUFLIA`, `QF_AX` | — | blocked: arrays |
| `AUFLIRA`, `AUFNIRA` | — | blocked: arrays (and the only standard logics with both Int and Real) |
| `QF_BV`, `QF_UFBV`, `QF_ABV`, `QF_AUFBV` | — | blocked: bit-vectors |
| `QF_EIA` | — | blocked: exponentiation |

**Observed features cross-check.** Each rule handler returns the `Features` it used;
`produce_lambdapi_proof` accumulates them. The header still comes from `set-logic`, but the two
sets are compared: if the observed set exceeds the declared one, widen the header and warn; if it
falls short, the declared logic simply over-imports, which is harmless but worth reporting.

This is not defensive clutter, because **the declared logic is necessarily an over-approximation**
— a direct consequence of the gaps in the standard's name list. The tlaps corpus is the example:
all 56 files declare `UFNIA`, and given that there is no `UFLIA` in the standard, `UFNIA` is in
fact the *correct* standard name for quantified UF + integer arithmetic without arrays (the
alternative, `AUFLIA`, would falsely claim arrays). The proofs nevertheless use only
`la_generic`, `la_disequality`, `la_mult_neg` and `comp_simplify` — linear reasoning throughout.
The same holds for `benchmarks/small`: 992 `AUFLIA` + 619 `AUFLIRA` problems name array support
their proofs may never touch. Rejecting those on the logic name alone would refuse proofs that
translate perfectly well.

The cross-check also covers what the logic string cannot express at all: `logic: None`, and `ALL`
— which is not a standard logic but is what carcara prints by default
([printer.rs:702](src/ast/printer.rs#L702)), what `sat_refutation` synthesises
([sat_refutation.rs:255](src/checker/sat_refutation.rs#L255)), and what the `tests/rules/rare.rs`
fixtures declare.

Wiring: `prelude.logic` is already in hand at
[mod.rs:163](src/translation/lambdapi/mod.rs#L163) and simply never read. `ProofFile.requires` is
assigned at :170 *before* `translate_commands` at :185 — move that assignment after the body is
built. `Config` ([mod.rs:48-51](src/translation/lambdapi/mod.rs#L48-L51)) is currently dead and
can host an override flag.

Optional, recommended as a build-time check only: one-line facade modules
`alethe-lp/logics/QF_LIA.lp` = `require open alethe.core alethe.prop lambdapi.la
alethe.lia;`, one per in-scope logic (11, plus the 4 partial ones). Building them under `make`
verifies that each supported logic's module combination type-checks *together*, at library build
time rather than at proof-check time — which is where a numeral-binding conflict would show up if
one is ever introduced. Keep the generated header as the explicit module list (one code path); a
Rust test asserts the table and the facade files agree.

## 4. Rule → module

**core** — assume, hole, subproof, let, bind_let, not_not, resolution, th_resolution, tautology,
contraction, weakening, reordering, refl, symm, not_symm, trans, cong, eq_reflexive,
eq_transitive, eq_congruent, eq_congruent_pred, eq_symmetric, distinct_elim, eq_simplify.

**prop** — true, false, and, or, not_and, not_or, and_pos, and_neg, or_pos, or_neg, xor1/2,
not_xor1/2, xor_pos1/2, xor_neg1/2, implies, not_implies1/2, implies_pos, implies_neg1/2,
equiv1/2, not_equiv1/2, equiv_pos1/2, equiv_neg1/2, ite1/2, ite_pos1/2, ite_neg1/2, not_ite1/2,
connective_def, bfun_elim, ite_intro, and_intro, and_simplify, or_simplify, not_simplify,
implies_simplify, equiv_simplify, bool_simplify, ite_simplify, ac_simp, aci_simp, nary_elim,
all_simplify, `rare_rewrite`/`multi_rare_rewrite` (bool-* names), `shuffle` and `evaluate` (∧/∨
case).

**quant** — bind, sko_ex, sko_forall, forall_inst, qnt_cnf, qnt_simplify, onepoint, qnt_join,
qnt_rm_unused, miniscope_distribute/split/ite.

**la** — la_generic (steps 1,2,3,5), la_disequality, la_totality, la_tautology, la_mult_pos,
la_mult_neg, la_rw_eq, sum_simplify, prod_simplify, minus_simplify, unary_minus_simplify,
comp_simplify, div_simplify (statement), `shuffle`/`evaluate`/`rare_rewrite` (`arith-*`, generic).

**lia** — la_generic step 4 (integer strengthening), lia_generic, mod_simplify, integer `div`
folding, ℤ-only `arith-int-*` RARE.

**lra** — ℚ literal rendering, real `/` folding.

**unsupported** — bitblast_extract … bitblast_not (14 rules) and any array/string/FP/datatype
rule: `TranslatorError::UnsupportedRule`.

Changes against the fragment proposal's table worth flagging: `not_not`/`tautology` and
`eq_simplify` move into `core`; `let`/`bind_let` move from quantifiers into `core`; `shuffle`,
`nary_elim` and `evaluate` are split by operator rather than assigned to one module; the `rare`
and `rare_arith` modules disappear into `prop` and `la`/`lia`.

## 5. Frictions this layout creates

1. **Theory-polymorphic rules.** `shuffle` (∧/∨ *or* +/×), `nary_elim`, `evaluate`,
   `all_simplify`, `rare_rewrite`, `eq_simplify`, `div_simplify`, `comp_simplify` and `la_generic`
   (Int vs Real) all branch on the principal operator's sort. One rule name, two modules. The
   dispatch table maps the name to a handler which branches on `pool.sort(…)` and delegates
   (`prop::shuffle` → `la::shuffle_arith`). This is a Rust-side edge only — `la.lp` never requires
   `prop.lp`, so the `.lp` graph stays a forest. Unavoidable in any decomposition; the coarse one
   just makes it visible.
2. **RARE provenance vs. theory.** RARE rewrites are cvc5-version-specific and machine-named
   (`bool-and-flatten`); theory-wise they belong in `prop`/`la`, provenance-wise they want a
   separately regenerable file. Recommendation: keep them in the theory modules inside a
   comment-delimited `// ─── cvc5 RARE (regenerated) ───` region, and split only if regeneration
   is ever automated. Note eight of them are already aliases of `Simplify.lp` lemmas.
3. **The deepest existing coupling is `int2nat`.** The n-ary clause rules (`and_pos`, `not_or`,
   `or_neg`, `disj_resolutionN*`) express their ℕ index arguments through `int2nat`, which lives
   in [Lia.lp:12](alethe-lp/Lia.lp#L12) — so *pure QF_UF steps currently need a symbol from
   the arithmetic module* ([term.rs:1143-1147](src/translation/lambdapi/term.rs#L1143-L1147)).
   `int2nat`/`pos2nat` must move to `core.lp` in Stage 1, or the QF_UF header cannot drop `lia`.
4. **Mixed Int+Real would open `lia.lp` and `lra.lp` together**, and both bind `"0".."10"`; last
   loaded wins. This is less pressing than it first appears: the only standard logics with both
   Int and Real are `AUFLIRA` and `AUFNIRA`, and **both also require arrays**, so mixed
   arithmetic is gated behind array support that does not exist. It remains reachable through
   `ALL`, through a missing `set-logic`, and through non-standard names solvers accept — i.e.
   exactly the paths the observed-features cross-check is watching. Defer the fix (bind numerals
   in neither module and emit qualified constructors) until arrays or a concrete mixed-arithmetic
   proof forces it; until then, make the combination *fail loudly* rather than silently mis-bind,
   which the cross-check warning does.
5. **`core.lp` cannot be made ℤ-free by reordering alone.** [Alethe.lp:2](alethe-lp/Alethe.lp#L2)
   and [Clause.lp:2](alethe-lp/Clause.lp#L2) open `Stdlib.ExtraRules`, which itself does
   `require Stdlib.Pos as P; require Stdlib.Z as Z;`. ℤ is therefore *loaded* (its builtin table
   merged) even though `Alethe.lp`/`Clause.lp` reference zero ℤ symbols — which is exactly why the
   ℕ-restoring workaround at Alethe.lp:9-21 exists. After the split a QF_UF proof would open only
   `core`+`prop` and have no ℤ symbol and no ℤ numeral *in scope*; making ℤ genuinely unloaded
   needs an upstream `Stdlib` change (a Bool+Nat+List-only rules module). Target the achievable
   invariant: **the core layer binds no numerals.**
6. **Arrays, not bit-vectors, are the missing feature that matters.** Of the 25 standard logics,
   this architecture fully serves 11 and partially serves 4; of the 10 it cannot serve, **7 are
   blocked on arrays** and 2 on bit-vectors alone. The corpus agrees: 1611 of the 1639 small
   benchmarks are `AUFLIA`/`AUFLIRA`, and there are no bit-vector benchmarks at all — so the
   fragment proposal's `bv.lp` stub would have covered the least valuable feature. Recommendation:
   create **no stub `.lp` files**. Keep `Feature::{Array, Bv, Nonlinear, Exp}` in `logic.rs` so the
   parser is total and the diagnostic names the actual blocker; create a file when there is
   content to put in it. If a feature is added next, it should be arrays.
7. **`core.lp` and `prop.lp` are both ~1600 lines.** That is the price of coarseness; mitigate
   with private helper files under transitive `open` if it becomes unpleasant.

## 6. Migration

Each stage keeps `make -C alethe-lp` green and the tlaps test at its baseline.

**Stage 0 — dead code, no behaviour change. DONE.** Deleted the orphan files `Lia.lpi` (622
lines, never compiled), `LiaAC.lp` (249), `Naryfun.lp` (95, superseded by `Stdlib.NaryFun`) and
`Zgcd.lp` (134, superseded by `Stdlib.Zgcd`); the three commented-out blocks in `Alethe.lp`
(`1307-1398`, `1725-1942`, `1953-2079` — 436 lines of superseded reification designs); the
`cong..cong5` family; the leaked test symbols (`Clause.lp:91-92` declared non-private `a`/`b`
that entered every generated proof's namespace); and, on the Rust side, `translate_rule_name`,
`LTerm::Resolution`, `AxiomsFile`, `get_dependencies_map` and `PrettyPrintAx`.

Two corrections to what this stage was expected to be:

- **`feq` is the live family, not `cong`.** The Rust `cong` handler emits `feq`, `feq2`,
  `feq{arity}` ([tautology.rs:522-582](src/translation/lambdapi/tautology.rs#L522-L582)), and
  `feq`/`feq2` are used inside `Alethe.lp`, `Clause.lp`, `La.lp`, `Lia.lp` and `Rat.lp` proofs;
  nothing referenced `cong..cong8` at all. So `cong..cong5` was deleted and **`cong6/7/8` were
  renamed `feq6/7/8`** — which also fixes a latent bug: the translator emitted `feq{n}` for
  n ∈ 6..8 while only `feq..feq5` existed, so `cong` on a 6-ary function produced an unbound
  symbol.
- **`Stdlib.Zgcd` is not a drop-in for the local `Zgcd.lp`.** It provides `red_by_Stein` on ℙ but
  no ℤ wrapper, so `Z_red_Stein` (11 lines, used only by the ℚ normal form) moved into `Rat.lp`.

`Makefile`'s `clean` was also changed from `rm -f $(OBJ)` to `rm -f *.lpo`, since the former is
derived from the `*.lp` wildcard and so leaves orphaned `.lpo` files behind after a module is
deleted — stale artifacts that keep a dangling `require` resolving.

**Stage 1 — split the stdlib mechanically. DONE.** `Alethe.lp`, `Clause.lp`, `Tactic.lp`,
`Simplify.lp`, `Rare.lp`, `Lia.lp` and `La.lp` became `core.lp` (1611), `prop.lp` (1488),
`quant.lp` (203), `lia.lp` (880) and `lra.lp` (483), with `Rat.lp` kept as a support file —
5034 lines across 6 files, from 5038 across 8. Declaration blocks moved verbatim; the only
edits were the ones forced by merging (below). `gen_required_module` now emits
`lambdapi.{core,prop,quant,lia}` as a temporary hard-coded list.

Four things this stage had to resolve that the plan did not anticipate:

- **`la.lp` is deferred to stage 5.** Nothing in today's arithmetic is carrier-generic: `Lia.lp`
  reifies directly over ℤ, and the `la_*` rules in `Rare.lp:481-514` are stated over ℤ too. A
  carrier-generic `la.lp` cannot be produced by moving blocks, only by the `LinOrd`
  generalisation, so `lia.lp` currently holds both halves and `la.lp` appears in stage 5.
- **`int2nat`/`pos2nat` stay in `lia.lp`,** so friction 3 is not yet resolved and a quantifier-free
  proof still opens `lia`. They are typed over ℤ/ℙ, so hosting them in `core` would force
  `core` to `open Stdlib.Z`, putting ℤ's `+` and `*` in scope beside ℕ's. The real fix is to stop
  emitting `int2nat n ⊤ᵢ` for clause indices, which belongs with the numeral strategy in stage 4.
- **`lia.lp` opens `core` mid-file.** Its reification half shares 19 names with the clause
  machinery in `core` (`compN`, `split`, `merge`, `mergesort`, `case`, `index`, `rec_𝕃`, …), so it
  is compiled before `core` is in scope — mirroring the fact that `Lia.lp` is standalone today and
  only `Rare.lp`'s second half opens `Alethe`. The ℤ numeral pin is repeated after that open, as
  `Rare.lp:225-235` does. One reference had to be qualified: `Stdlib.Comp.opp`, which would
  otherwise resolve to the reification half's `opp ≔ mul (— 1)`.
- **Two same-name-different-statement collisions had to be broken.** `case_l` is declared by both
  `Alethe.lp` and `Clause.lp` with the inequality flipped; the `Clause.lp` one became
  `case_l_size`. `and` is declared by both `Alethe.lp` (the rule) and `Tactic.lp` (the tactic
  combinator `≔ &`); the Alethe one turned out to be dead — the translator emits `∧ₑₙ` — so
  `eq`, `In_∧`, `In_∨`, `In_∧'`, `In_∨'`, `and` and `test_and` were deleted together, which
  removes the collision rather than renaming around it.

A practical warning for anyone repeating this: **the default macOS filesystem is
case-insensitive**, so `lia.lp` and `Lia.lp` are the same file. Two distinct failures follow. A
generator that writes `lia.lp` while still reading `Lia.lp` silently consumes its own output. And
git keeps the *old* casing in the index, so the tree ended up tracking `Lia.lp` while the disk
held `lia.lp` — invisible on macOS, but a Linux clone would get `Lia.lp` and fail to resolve
`require open alethe.lia`. Check `git ls-files` against `ls` after any rename that changes case.

**Stage 2 — Rust move, mechanically. DONE.** `term`, `proof`, `dsl`, `printer` and `output`
moved under `syntax/`; `tautology.rs`, `simp.rs` and `lia.rs` were split into `rules/core.rs`
(644), `rules/prop.rs` (976), `rules/quant.rs` (53) and `rules/lia.rs` (744), with
`rules/mod.rs` holding the shared catch-all. Function bodies are unchanged; the seven unit tests
followed their handlers (five to `core`, two to `prop`). The only edits were import paths —
`use super::*` in the moved files used to reach `mod.rs`'s scope, so `std::fmt`,
`itertools::Itertools` and `match_term_err` became explicit imports.

`rules/la.rs` and `rules/lra.rs` do not exist yet, matching the library: they arrive with the
`LinOrd` generalisation in stage 5. The resolution and subproof machinery is still in `mod.rs`
because it is entangled with the `translate_commands` loop; it moves to `rules/core.rs` in
stage 3, where that loop is replaced anyway.

**Stage 3 — one dispatch table. DONE.** The five-arm guard chain and `translate_tautology` are
replaced by `rules::translate_step`, a single `match` returning
`(Option<Vec<ProofStep>>, Features)`. The `rule.contains("simp")` guard is gone, so the 13 rules
that used to reach `unimplemented!` no longer panic. `TranslatorError::UnsupportedRule` exists and
the `_` arm returns it, with `Config::admit_unsupported` mapping it to `admit` instead.

The catch-all could not simply become an error: ~40 rules are proved by a library lemma of the
same name and rely on `apply <rule> <premises>`. That set is now the explicit `LEMMA_RULES`
constant, **derived from the library** by intersecting the checker's rule table with the symbols
declared in `core/prop/quant/lia.lp`, and a unit test re-checks that every name in it is really
declared — so a rule can no longer silently emit an unbound identifier that surfaces only at
`lambdapi check` time. Rules knowingly left unproved are likewise explicit in `ADMITTED_RULES`
rather than hidden in a catch-all.

The `?` on `premises.first()` used to make a step vanish from the output when premises were
missing; it now returns `PremisesError`. The `is_end_step()` break, previously reachable only from
the tautology arm, now applies to every step arm — a resolution as the last step of a subproof
would otherwise have run the inner loop into the parent's steps.

The resolution family (`translate_resolution`, `make_resolution`, `remove_pivot_in_clause`,
`get_pivots_from_args`, `term_negated`) moved to `rules/core.rs`. `translate_subproof` stayed in
`mod.rs`: it handles the `ProofCommand::Subproof` *command* and drives the loop, rather than
dispatching a rule.

**Stage 4 — `logic.rs`. MOSTLY DONE.** `Features`, `features_of_logic` and `modules` are in, with
the 25 standard logics as an exhaustive table and six unit tests over it. `produce_lambdapi_proof`
now reads `prelude.logic`, seeds the features from it, widens them as rules are translated, emits
the header from the result, and warns through `report_logic` when a proof used a feature its logic
did not declare — the check that finds a mislabelled benchmark.

One refinement the plan did not foresee: **`alethe.lra` is gated on *observed* real arithmetic,
never on the declaration.** An unrecognised logic declares every feature, and `lia` and `lra` both
rebind the decimal notation, so taking `lra` from the declaration would leave numerals ambiguous
in every proof that lacks a `(set-logic …)`. Over-importing `quant` on the same basis is harmless
and is still allowed.

`carcara translate lambdapi <proof> <problem>` now exists (`TranslationTarget::Lambdapi`), so the
backend is reachable outside the test harness for the first time: it elaborates, translates and
prints the module on stdout, with `--admit-unsupported` mapping unimplemented rules to `admit`.
`--eunoia-mech` became optional, since it is meaningless for this target.

The per-logic facade modules are **not** written, and are not worth writing yet: while
`alethe.lia` is unconditional (friction 3), every in-scope logic maps to one of only two module
sets, so the build-time check they would provide is vacuous. They become useful once `int2nat`
moves and `lia` is gated on `Features::INT`.

**Stage 5 — arithmetic.** `LinOrd` in `la.lp`, `ℤ_lin`/`ℚ_lin`, then Real support end to end
(`BuiltinSort::Real`, `translate_sort_function`, ℚ literal rendering, stop truncating
`Constant::Real`) and `lra.lp`. Then move `la_mult_pos/neg`, `la_rw_eq`, `la_tautology` off
`admit`.

**Stage 6 — `alethe-lp/README.md`. DONE.** The module table, the placement rule, the
logic→module table for all 25 standard logics, the numeral-ordering constraint, and a per-module
count of the remaining `admit`s and axioms (26 admits and 28 axioms in total, 15 of the admits in
`Rat.lp` alone, which is what `lra.lp` would rest on).

## Verification

- `make -C alethe-lp` after every stage — each module compiling in isolation also validates
  that the `require` graph is acyclic and minimal.
- `cargo +1.93 test --release --test test_example_files tlaps`. **Baseline is 53/55**; the two
  failures are carcara elaborator panics (`elaborator/polyeq`, via `elaborate_assume` on a `bind`
  subproof), not Lambdapi issues. `tests_tautolog::test_cong_{and,or}_translation` already fail on
  clean HEAD — do not read them as regressions.
- Diff generated `.lp` output on the tlaps proofs before/after Stages 1-3: **only the `require
  open` header should change.**
- New tests: (a) `features_of_logic` against **all 25 standard logic names**, plus `None`, `ALL`
  and a non-standard name, asserting the expected module list for each; (b) dispatch
  coverage — every rule in `get_rule` ([shared.rs:199](src/checker/shared.rs#L199), 178 arms) is
  either dispatched or in an explicit `UNSUPPORTED` set; (c) every dispatched rule's module is in
  its feature's dependency closure; (d) the `logic.rs` table agrees with the `logics/*.lp` facades.

## Open item

**`Rat.lp`.** The decision was to rebase on `Stdlib.Zgcd` and `Stdlib.NaryFun` but not
`Stdlib.MergeSort`; `Rat` was not covered either way, so this plan keeps the local `Rat.lp`,
retargeted to `Stdlib.Zgcd`. Worth settling before Stage 5: it is a 357-line fork of the 228-line
`Stdlib.Rat` (the extra content is the `ℚ : TYPE` / `rat : Set` / `τ rat ↪ ℚ` encoding bridge plus
lemmas), and **15 of the 17 lemmas in its `240-358` range are `admit`ted** — so wiring `lra.lp` on
top of it produces proofs that check only because of those admits. Rebasing on `Stdlib.Rat` and
keeping only the encoding bridge is the alternative.
