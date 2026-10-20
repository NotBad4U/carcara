# `la_generic` as one tactic: a reflective certificate checker

*Branch `lambdapi-refactor`, 2026-10-20. Files: `lia.lp` (ℤ, lines 713–1205 and the smoke
test at the end), `lra.lp` (ℝ, lines 998–1367), `src/translation/lambdapi/rules/{lia,lra}.rs`,
`syntax/printer.rs`, `rules/prop.rs`.*

## 1. The problem

An Alethe `la_generic` step is a clause of linear (in)equalities `φ₁ … φₙ` that is a tautology
because a linear combination of the negated literals, with the step's `:args a₁ … aₙ` as
coefficients, is a contradictory constant (the Farkas lemma). Until now the translator proved
each such step with a tactic script that replayed the Alethe algorithm literal by literal:

```
rewrite .[x in _ ∨ … ∨ x] <_eq_¬_≥;           // step 1: negate a positive literal
try rewrite ≤_opp_eq;                          // flip < and ≤ into > and ≥
rewrite ≥_sub_eq (lhs) (rhs);                  // step 3: s₁ ⋈ s₂ into s₁ - s₂ ⋈ 0
rewrite >_eq_≥_succ (s) (0);                   // step 4: s > 0 into s ≥ 0 + 1 (ℤ only)
rewrite ¬_≥_compat_mul_pos_l_eq (c) (s) (0) ⊤ᵢ; // step 5: scale by the coefficient
rewrite imp_eq_or; assume H0;                  // step 2: each literal is a hypothesis
set H0l' ≔ …; set H0r' ≔ …;                    // name the sides
have sum : π (l ≥ r) { refine (≥_add_≥ … (≥_add_≥ …)) };   // sum them
rewrite left reify_correct l; … rewrite left norm_correct …; refine ⊤ᵢ;   // reflective tail
```

That is ~10 tactic lines *per literal*, every one elaborated by Lambdapi's `rewrite`, and only
the last three lines were computation. The 12-literal `t50` of `pigeon-hole-5` was ~120 lines.
The thesis (ch. 12) measured this `rewrite` chain as the main cause of LIA timeouts: the same
normalisation succeeds instantly with `compute`.

Lambdapi has no `lia`. Its tacticals cannot provide one either (checked against
`src/handle/tactic.ml` of the installed `dev-3.0.0-156`): tactic terms never see the goal;
`repeat t` is unbounded and stops only when `t` fails or the goal count drops, so
`#repeat (#rewrite ≥_sub_eq)` loops on its own output (`a - b ≥ 0` matches `_ ≥ _` again);
`try`/`orelse` do not roll back metavariable assignments; `#refine` takes only a string
literal; `why3` has no arithmetic theory. The per-literal lemmas also need their arguments
instantiated, so a tactical combination stays a generated per-literal script.

## 2. The idea

Rocq's `lia` (micromega) does not search inside the kernel: it checks a Farkas certificate by
reflection. Alethe already gives us the certificate — the `:args`. So the shape is the same:

```
      Alethe step                     Lambdapi
  (cl φ₁ … φₙ) :args (a₁ … aₙ)   ⟼   refine (Zla_generic (a₁ ⸬ … ⸬ □) (φ₁ ⸬ … ⸬ □) ⊤ᵢ);
```

1. **Reify** the clause into a syntax (`rfy_clause`), by rewriting.
2. **Check** the certificate: a boolean `check cs lits` scales the negated literals, sums them,
   normalises the sum with the existing `norm_speed`, and reads the sign of the constant.
   `⊤ᵢ : π ⊤` discharges `istrue (check …)` because it *computes* to `⊤`.
3. **Soundness**, proved once: `check cs lits = true → denote_clause lits env`.
4. The type of `Zla_generic cs G ⊤ᵢ` is `π (denote_clause (rfy_clause □ G ₁) (rfy_clause □ G ₂))`,
   which the kernel's ordinary conversion reduces to `π̇ G`, the step's goal.

The same mechanism as `#cauto` (`tauto.lp`), minus one thing, by user decision: **no
`unif_rule`**. The clause `G` is passed explicitly (the Rust prints it anyway, with the shared
`p_N` names) instead of being recovered from the goal by unification as `tauto_aux [goal]`
does; `refine` needs no unification rule at all. The `#apply`-based tactic-term sugar was
dropped for the same reason (its `η a` argument is resolved by core.lp's unif rules).

## 3. The ℤ library (`lia.lp`)

Everything sits **before** `require open alethe.core` (line 1206): after that line the numerals
`0..10` are ℕ and `index`/`case`/`and` are core's.

### 3.1 Expression syntax (lines 733–840)

A transliteration of `lra.lp`'s `Expr` to ℤ:

```
inductive ZExpr ≔ ZEAdd | ZEOpp | ZECst : ℤ → ZExpr | ZEMul : ℤ → ZExpr → ZExpr | ZEMulr | ZEAtom : ℕ → ZExpr
zdenote : ZExpr → 𝕃 int → ℤ                    // the term again, atoms looked up with nth
sequential symbol rfyE : 𝕃 int → ℤ → τ (zexpr × list int)   // reification, threading the atom list
zlin : ZExpr → 𝕃 grp                            // the monomial list norm_speed sorts
```

Why a new reifier next to the existing `rfy`/`reify` (which target `𝕃 grp` directly)? Because
`zdenote (rfyE l x ₁) (rfyE l x ₂)` is `x` again **by computation** — `zdenote (ZEAtom i) l`
reduces to `nth l i`, which reduces to the atom — whereas `val (reify x) = x` is a lemma
(`reify_correct`, by induction): `x * 1 + 0` does not reduce to `x` for a variable `x`. The whole
design rests on the reified clause denoting back to the clause by conversion, so no lemma
`zdenote (rfyE x) = x` is ever stated (and none could be, for a sequential reifier whose
catch-all fires on variables: see the memory note on `index`). The old reifier stays:
`poly_norm_eq` and `rare/lia.rs` use it.

`mul_correct`, `opp_correct`, `zlin_correct` relate `val` of the linear form to `zdenote`.

### 3.2 Literal and clause syntax (lines 841–910)

```
inductive BRel ≔ BEq | BLt | BGt
inductive ZLit ≔ LRel : BRel → ZExpr → ZExpr → ZLit | LNeg : ZLit → ZLit | LTop | LBot
denote_lit (LRel BLt a b) l ↪ istrue (isLt (zdenote a l ≐ zdenote b l))
denote_lit (LRel BGt a b) l ↪ istrue (isGt (zdenote a l ≐ zdenote b l))
denote_lit (LRel BEq a b) l ↪ zdenote a l = zdenote b l
denote_lit (LNeg x) l ↪ ¬ (denote_lit x l)       denote_lit LTop/LBot ↪ ⊤/⊥
denote_clause : 𝕃 zlit → 𝕃 int → Prop            // φ₁ ∨ (φ₂ ∨ … ∨ ⊥), the shape of core's disj
```

**Why these three relations and not `≤ < ≥ >`.** In `Stdlib.Z`, `<`, `≤`, `≥`, `>` are
*definitions* (`< x y ≔ istrue (isLt (x ≐ y))`, `≤ x y ≔ ¬ istrue (isGt (x ≐ y))`,
`≥ x y ≔ ¬ (x < y)`, `> x y ≔ ¬ (x ≤ y)`), and so is `¬ p ≔ p ⇒ ⊥`. A rewrite rule cannot match
a defined symbol: it is unfolded before matching (the reason `lia.lp`'s old
`rfy $l ($x - $y)` rule was dead code). So the reifier `rfy_lit` matches the *stuck* shapes
`istrue (isLt (a ≐ b))`, `istrue (isGt (a ≐ b))`, `@= int a b`, `$p ⇒ ⊥`, `⊤`, `⊥`, and the
denotation produces exactly those, so that conversion closes the loop. The resulting shapes:

| printed literal | reified as |
|---|---|
| `a < b` | `LRel BLt a b` |
| `a ≥ b`, `¬ (a < b)` | `LNeg (LRel BLt a b)` |
| `a ≤ b` | `LNeg (LRel BGt a b)` |
| `a > b`, `¬ (a ≤ b)` | `LNeg (LNeg (LRel BGt a b))` |
| `0 ≤ 1` (numerals compute: `⊥ ⇒ ⊥`) | `LNeg LBot` |

`LTop`/`LBot` exist because a comparison between numerals computes to `⊤`/`⊥` before the
reifier sees it. `rfy_lit` is `sequential` only to silence the critical pairs this overlap
creates; it has no catch-all, so no rule fires on a variable. In-file `assert`s check the table
above and that `denote_clause (rfy_clause □ C ₁) (rfy_clause □ C ₂) ≡ C₁ ∨ … ∨ ⊥` on the shapes
the translator prints (`Stdlib.Z.-1 * (x + y)`, `a - b`, right-nested `+`, dag names `p_N`).

### 3.3 The checker (lines 911–1000)

The hypotheses are the *negations* of the clause's literals. Each is put in the form
`s ⋈ 0`, `s : 𝕃 grp`, `⋈ ∈ {=, ≥}` — over ℤ a strict `s > 0` is tightened to `s - 1 ≥ 0`
(Alethe step 4), so `>` never survives:

```
inductive Cmp ≔ Ceq | Cge          hyp_val v Cge ↪ v ≥ 0 ; hyp_val v Ceq ↪ v = 0
neg_s (LRel BLt a b) ↪ zlin a ++ opp (zlin b)                    // ¬(a<b): a - b ≥ 0
neg_s (LRel BGt a b) ↪ zlin b ++ opp (zlin a)                    // a ≤ b: b - a ≥ 0
neg_s (LRel BEq _ _) ↪ □                                         // a ≠ b: unusable, 0 ≥ 0
neg_s (LNeg x) ↪ pos_s x    pos_s (LNeg x) ↪ neg_s x
pos_s (LRel BLt a b) ↪ zlin b ++ opp (zlin a) ++ (Cst (— 1) ⸬ □)  // a < b: b - a - 1 ≥ 0
pos_s (LRel BGt a b) ↪ zlin a ++ opp (zlin b) ++ (Cst (— 1) ⸬ □)  // a > b: a - b - 1 ≥ 0
pos_s (LRel BEq a b) ↪ zlin a ++ opp (zlin b)                    // a = b: a - b = 0  (Ceq)
coef c Ceq ↪ c ; coef c Cge ↪ zabs c                             // the rule's a / |a|
combine_s (c ⸬ cs) (x ⸬ xs) ↪ mul (coef c (neg_k x)) (neg_s x) ++ combine_s cs xs
combine_k … ↪ join (neg_k x) (…)                                  // Ceq only if every literal is
contra : 𝕃 grp → Cmp → 𝔹      // on a normal form: Cst k ⸬ □ with k < 0 (both), k > 0 (Ceq only)
check cs ls ≔ contra (norm_speed (combine_s cs ls)) (combine_k cs ls)
```

`neg_s`/`pos_s` come in pairs so that `LNeg` just swaps them. A literal without a coefficient
is dropped (`combine_s _ □ ↪ □`), which only weakens the sum. `assert`/`assertnot` lines check a
valid certificate, a wrong one, and Carcara's gcd-strengthening fixture (expected to fail,
§7).

### 3.4 Soundness (lines 1001–1205)

```
ge_sound a b : π (¬ (a < b)) → π (a + — b ≥ 0)                    // ≥_sub
le_sound a b : π (¬ istrue (isGt (a ≐ b))) → π (b + — a ≥ 0)      // ≥_sub, ≥_≤
lt_sound a b : π (a < b) → π (b + (— a + — 1) ≥ 0)                // <_>, >_sub, >_0_eq_≥_1
gt_sound a b : π (istrue (isGt (a ≐ b))) → π (a + (— b + — 1) ≥ 0)
eq_sound a b : π (a = b) → π (a + — b = 0)
lit_sound l x : π ((¬ denote_lit x l ⇒ hyp_val (val (neg_s x ‚ l)) (neg_k x))
                 ∧ (denote_lit x l ⇒ hyp_val (val (pos_s x ‚ l)) (pos_k x)))
scale_sound v k : π (hyp_val v k) → Π c, π (hyp_val (coef c k * v) k)
add_sound v1 v2 k2 : π (hyp_val v2 k2) → Π k1, π (hyp_val v1 k1) → π (hyp_val (v1 + v2) (join k1 k2))
contra_sound l g k : π (istrue (contra g k)) → π (hyp_val (val (g ‚ l)) k) → π ⊥
check_sound, combine_sound, Zla_generic_sound cs ls l : π (istrue (check cs ls)) → π (denote_clause ls l)
```

Points worth knowing:

- `lit_sound` proves both directions at once — the conjunction is what makes the `LNeg` case go
  through (`∧ₑ₂ ih (¬¬ₑ _ h)` / `∧ₑ₁ ih h`). The `LRel` cases `change` the goal to expose
  `val ((zlin a ++ opp (zlin b)) ‚ l)` — `rewrite` is syntactic, it does not unfold `neg_s` —
  then rewrite `++_eq_+`, `opp_correct`, `zlin_correct` and `refine` the step lemma; `refine` is
  up to conversion, so the unreduced `— 1 + 0` is fine there.
- `scale_sound`'s `Cge` case is an induction on the coefficient: `Z0 * v` computes to `Z0`,
  `Zpos p`/`Zneg p` use `≥_compat_mul_pos_l (Zpos p) v 0 (λ x, x ⊤ᵢ)` — the premise
  `Zpos p > 0` *computes* to `(⊤ ⇒ ⊥) ⇒ ⊥`. This is how `|c|` is handled without a side
  condition.
- `combine_sound` is a continuation-passing induction on the literal list: the continuation
  `… → π ⊥` plays the accumulator, so no partial-sum argument is needed. Each literal is either
  true, which proves the clause (`∨ᵢ₁`), or false (`em`, classical), which adds one hypothesis.
- `contra_sound` is a `case_𝕃2` on the normal form (nil / singleton / longer), then inductions
  on the monomial and its ℤ: `Zneg p ≥ 0` computes to `⊤ ⇒ ⊥`, so `hv ⊤ᵢ` closes it.
- Zero admits, zero axioms, no `unif_rule`. Nothing ever reduces `rfyE`/`rfy_lit` on a variable:
  the lemmas are about the syntax.

The entry point is `opaque` (only its type is ever used):

```
opaque symbol Zla_generic (cs : 𝕃 int) (G : 𝕃 o) :
  π (istrue (check cs (rfy_clause □ G ₁))) → π (denote_clause (rfy_clause □ G ₁) (rfy_clause □ G ₂))
```

and the smoke test at the end of the file proves `(cl (not (<= n m)) (<= n m))` with
`refine Zla_generic (Stdlib.Z.1 ⸬ Stdlib.Z.1 ⸬ □) (…) ⊤ᵢ`.

### 3.5 Two `induction` pitfalls met on the way

- Lambdapi's `induction` abstracts the rest of the goal as a `Prop` motive. A `Π k : Cmp` (no
  Set code) or a `Π c : ℚ` (quotient type; its binder does not fit FOL's unification rule)
  *after* the inducted variable makes that motive ill-formed ("Missing subproofs (2 subproofs for
  4 subgoals)"). `Π c : ℤ` and `Π cs : 𝕃 int` are fine. Fix: put such arguments before the
  inducted one, or split a helper (`add_sound_eq`, `rscale_sound_gt`).
- `rewrite` finds its instance syntactically: `change` to the reduced form first.

## 4. The ℝ port (`lra.lp`, lines 998–1367)

Same skeleton on `lra.lp`'s existing `Expr`/`rfy`/`denote`/`lin`/`mul_correct`/`norm_speed`,
with names prefixed `R…` so that mixed proofs (which open both modules) never clash in the
generated text. Differences:

- `≤ᵣ` is the primitive (axiomatic) relation; `≥ᵣ`, `<ᵣ`, `>ᵣ` are definitions, so
  `RRel ≔ RLe | REq`, and `a ≥ᵣ b` is `RLRel RLe b a`, `a <ᵣ b` is `RLNeg (RLRel RLe b a)`.
- No tightening: `RCmp ≔ RCeq | RCge | RCgt`, a strict hypothesis stays `>ᵣ`
  (`¬ (a ≤ᵣ b)` is `a - b > 0`), and the sum is strict if any summand is.
- `|c|` over ℚ by `qabs` on the class representative; a strict hypothesis scaled by `0` is
  downgraded to `≥` (`rscale_k`), since `0 · s > 0` is false.
- `rcontra` reuses `cst_neg` (≥) and `cst_nonpos` (>) and adds `cst_nonzero` (=), with
  `val_lt_zero`/`val_le_zero`/`val_ne_zero` and `Rge_lt_absurd`/`Rgt_le_absurd`.
- Nothing computes on ℝ: `zero ≥ᵣ zero` is `le_reflexive zero`, `lit k ＋ᵣ zero` needs
  `add_zero_r`, etc.

## 5. The Rust side

`rules/lia.rs::gen_proof_la_generic(clause, args, ctx)` and the `lra.rs` twin are now ~15 lines:

```rust
let coefficients = Term::Alethe(LTerm::List(List(integer_coefficients(args).into_iter().map(Term::Int).collect())));
let clause = Term::Terms(vec![Term::Alethe(LTerm::Clauses(clause.iter().map(|t| ctx.get_or_convert(t).0).collect()))]);
vec![ProofStep::Refine(terms![Term::from("Zla_generic"), coefficients, clause, intro_top()], SubProofs(None))]
```

- ℤ coefficients are the `:args` scaled by the lcm of their denominators (the thesis's
  pre-step; cvc5 prints `1/1`). A Farkas certificate is invariant under positive scaling. The
  ℝ generator prints them as `n / d` with the shared `lra::coefficients`.
- The clause is printed with the shared `p_N` names (`ctx.get_or_convert`), like the step's
  own type.
- `rules/mod.rs` passes `ctx` instead of `pool`. The 440-line script generator, `sum_hyps`,
  `Op`, `ReifiedInequality`, `get_inequalities_from_clause`, `sum_hyps_with` are deleted.
- Coefficients that Carcara infers (`bounded_farkas`) never reach the backend: the `Local`
  elaboration pass, which `translate` runs, rewrites those steps into `la_generic` with full
  `:args` first.
- Unit tests (lia.rs: 3 new; lra.rs: the 2 script tests rewritten) assert the single `refine`
  line, the lcm scaling, and that signs/denominators are kept.

### 5.1 A printer bug found by this work

`PrettyPrint for List` (`syntax/printer.rs`, the CLI printer) printed every list **reversed**,
while the `Display` impl (used by the unit tests) printed it in order; `rules/prop.rs`
compensated by pre-reversing its seven lists. The unit tests passed and the CLI emitted
`(1 ⸬ 1 ⸬ -1)` for `:args (-1 1 1)`, which broke `unsat-11-arith`. Both printers now preserve
order and the compensation is gone. Lesson (already in the memory notes): the CLI prints via
`printer.rs`, not `Display`; prototype from CLI output.

## 6. Results

- `lia.lp`, `lra.lp`: 0 errors, no new admits/axioms/critical pairs.
- `cargo +1.93 test`: 179 lib tests. (The `small_bv_*` integration tests fail on this branch
  before and after: Carcara's checker lacks `bv_bitblast_step_var` here.) Clippy: 23 → 22.
- Corpus (`scripts/translate-benchmarks.sh`, logs read by hand — lambdapi exits 0 on errors):
  **29/31**, i.e. the 28 originals plus the three dsl-rewrite pigeon-hole proofs added to the
  gitignored `benchmarks/small/simple-tests/`; the two failures are the pre-existing §4.1.3
  ones (`unsat-00-distinct`, `unsat-05-simplify`, "proof is not finished"). None of the 28
  originals has an *integer* `la_generic`; the pigeon-hole proofs are the ℤ coverage,
  `unsat-11-arith`'s two steps the ℝ coverage.
- pigeon-hole-{2,4,5}: strict, 0 errors, only the `la_mult_neg` admits remain; modules ~22 %
  smaller; whole-module check 1.26→1.10, 1.76→1.17, 2.17→1.25 s (≈1 s of each is library
  loading).
- Negative control: an all-zero certificate on `t50` is rejected
  (`⊤ is not unifiable with ⊥`). Doubling one coefficient of `t50` is *not* rejected, and
  rightly so: literal 12 is cvc5's own summary inequality, whose variables cancel internally.

## 7. Not done, by design

- **gcd strengthening.** Carcara's checker tightens a strict integer literal by the gcd of its
  coefficients (`checker/rules/linear_arithmetic.rs:201`); the checker here does the plain
  `+1`, like the old script. Carcara's "Edge case" fixture is therefore rejected, as before.
  Planned as a verified certificate: `pos_s` would apply
  `tighten s ≔ if divides_all g s then s ++ (Cst (— Zpos g) ⸬ □) else s ++ (Cst (— 1) ⸬ □)` with
  `g` from `zgcd.lp`'s Stein gcd, and only the multiplication check `divides_all` needs a lemma.
- **Searching for the coefficients** (a real `lia`): would be an untrusted
  `farkas : 𝕃 zlit → 𝕃 int` (Fourier–Motzkin with fuel) plugged in as
  `Zla_generic (farkas (rfy_clause □ G ₁)) G` — sound for free by `Zla_generic_sound`, but only
  useful for steps without a certificate, i.e. `lia_generic`, which Carcara elaborates away.
- `la_mult_neg`, the only admit left in the pigeon-hole proofs (the lemmas exist in both files).
- The old step lemmas (`≥_add_≥`, `<_opp_eq`, `¬_≥_compat_mul_pos_l_eq`, …) are kept: several
  are reused by the `Zpoly_rel_*` family.
