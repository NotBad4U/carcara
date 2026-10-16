/*
    This file provides the tactics #tauto and #cauto, a proof search for
    propositional calculus following Dyckhoff's contraction-free sequent
    calculus LJT.

      R. Dyckhoff, "Contraction-free sequent calculi for intuitionistic logic",
      Journal of Symbolic Logic 57(3), 1992.

    The search is reflective: the goal is reified into the datatype `form`,
    a boolean `prove` decides provability by rewriting, and `prove_sound`
    turns a successful search into a proof term.

    `#tauto` is intuitionistic. `#cauto` is classical: by Glivenko's theorem a
    propositional formula is a classical tautology iff its double negation is
    an intuitionistic one, so `#cauto` searches for `¬ ¬ G` and concludes with
    `¬¬ₑ`.

    Besides ⊤ ⊥ ∧ ∨ ⇒ ¬ ⇔, an equality between propositions (Alethe's Boolean
    `=`) is reified as `pEq` and searched as an equivalence. Any other formula
    is an atom, and two atoms are the same when they are convertible.

    `prove` is *not* structurally recursive (the left rules rebuild the
    context), and LJT's termination argument uses a multiset ordering that is
    not formalised here. We therefore bound the search depth by a fuel
    argument: the procedure is sound, and complete for LJT-derivable sequents
    provided the fuel suffices.
*/
require open Stdlib.Impred;
require open Stdlib.FOL;
require open Stdlib.Nat;
require open Stdlib.List;
require open Stdlib.Prod;
require open Stdlib.Tactic;
require open Stdlib.Classic Stdlib.PropExt;
// Not opened: core's `and` is a tactic combinator, which would shadow the
// boolean `and` of the search below.
require alethe.core;

// A module that contains string literals must carry the "String" builtin itself.
builtin "String" ≔ Stdlib.String.String;

inductive form: TYPE ≔
| pTrue: form
| pFalse: form
| pAnd: form → form → form
| pOr: form → form → form
| pImpl: form → form → form
| pOther: ℕ → form
| pEq: form → form → form // an equality between propositions
;

symbol pNot p ≔ pImpl p pFalse;

symbol pIff p q ≔ pAnd (pImpl p q) (pImpl q p);

symbol formS: Set;

rule τ formS ↪ form;


symbol not_found: Prop; // Just a simple opaque definition to represent an error message.

// A denotation function converts our syntax into a semantic value
// The σ is the context which contains the mapping from variables to Props.
symbol formD (σ: 𝕃 o) (p: form): Prop;
rule formD _ pTrue ↪ ⊤
with formD _ pFalse ↪ ⊥
with formD $ctx (pAnd $x $y) ↪  (formD $ctx $x) ∧ (formD $ctx $y)
with formD $ctx (pOr $x $y) ↪  (formD $ctx $x) ∨ (formD $ctx $y)
with formD $ctx (pImpl $x $y) ↪  (formD $ctx $x) ⇒ (formD $ctx $y)
with formD $ctx (pOther $i) ↪ nth not_found $ctx $i
with formD $ctx (pEq $x $y) ↪ (formD $ctx $x) = (formD $ctx $y);

private symbol a: Prop;
private symbol b: Prop;
private symbol f: Prop → Prop;

type (a ⸬ f b ⸬ b ⸬ □);

private symbol ctx ≔ (a ⸬ f b ⸬ b ⸬ □);

assert ⊢ formD ctx (pOther 0) ≡ a;
assert ⊢ formD ctx (pOther 1) ≡ f b;
assert ⊢ formD ctx (pOther 2) ≡ b;
assert ⊢ formD ctx (pOther 3) ≡ not_found;

// The prover only ever looks up ⊥ and atoms in the context.

symbol is_false : form → 𝔹;
rule is_false pFalse ↪ true
with is_false pTrue ↪ false
with is_false (pAnd _ _) ↪ false
with is_false (pOr _ _) ↪ false
with is_false (pImpl _ _) ↪ false
with is_false (pOther _) ↪ false
with is_false (pEq _ _) ↪ false;

symbol is_var : ℕ → form → 𝔹;
rule is_var $i (pOther $j) ↪ eqn $i $j
with is_var _ pTrue ↪ false
with is_var _ pFalse ↪ false
with is_var _ (pAnd _ _) ↪ false
with is_var _ (pOr _ _) ↪ false
with is_var _ (pImpl _ _) ↪ false
with is_var _ (pEq _ _) ↪ false;

symbol knows_false : 𝕃 formS → 𝔹 ≔ has is_false;

symbol knows_var (i: ℕ) : 𝕃 formS → 𝔹 ≔ has (is_var i);

symbol All: 𝕃 formS → form ≔ foldr (pAnd) pTrue;

///////////////////////////////////////////////////////////////////////////////
// Proof search (LJT)
///////////////////////////////////////////////////////////////////////////////

/* `prove n Γ g` decides the sequent Γ ⊢ g with at most `n` non-trivial steps.

   The search alternates two phases:

   - `prove` applies the *right* rules. ⊤R, ∧R and ⇒R are invertible, so they
     commit. ∨R, the axioms and ⊥L are not enough on their own, so an atomic,
     absurd or disjunctive goal falls through to the left phase.

   - `scan n done todo g` walks the context looking for a left rule to apply.
     `done` holds the hypotheses already visited, `todo` those still to visit;
     the context of the sequent is `done ++ todo`. The invertible left rules
     (⊥L, ⊤L, ∧L, ∨L, and the ⇒-left rules whose antecedent is ⊤, ⊥, ∧ or ∨)
     commit as soon as they are found. The two non-invertible ones —
     ⇒L on an atomic antecedent, and Dyckhoff's ⇒L on an implicative
     antecedent — are tried and, on failure, the scan resumes with the
     hypothesis parked in `done`.

   The principal formula is always *removed* from the context, which is what
   makes the calculus contraction-free: no hypothesis is ever duplicated.

   An equality `pEq x y` is handled as the equivalence `pIff x y`, i.e. as the
   conjunction of the two implications. */

symbol prove (fuel: ℕ):  𝕃 formS → form → 𝔹;

symbol scan (fuel: ℕ): 𝕃 formS → 𝕃 formS → form → 𝔹;

rule prove _0 _ _ ↪ false
// ⊤R
with prove (_ +1) _ pTrue ↪ true
// ∧R and ⇒R are invertible
with prove ($n +1) $Γ (pAnd $x $y) ↪
  let l ≔ prove $n $Γ $x in
  let r ≔ prove $n $Γ $y in
  l and r
with prove ($n +1) $Γ (pImpl $x $y) ↪ prove $n ($x ⸬ $Γ) $y
// axiom, then the left rules
with prove ($n +1) $Γ (pOther $i) ↪
  let in_context ≔ knows_var $i $Γ in
  let by_left_rules ≔ scan $n □ $Γ (pOther $i) in
  in_context or by_left_rules
// ⊥L, then the left rules
with prove ($n +1) $Γ pFalse ↪
  let in_context ≔ knows_false $Γ in
  let by_left_rules ≔ scan $n □ $Γ pFalse in
  in_context or by_left_rules
// ∨R is not invertible: try both disjuncts, then the left rules
with prove ($n +1) $Γ (pOr $x $y) ↪
  let l ≔ prove $n $Γ $x in
  let r ≔ prove $n $Γ $y in
  let by_left_rules ≔ scan $n □ $Γ (pOr $x $y) in
  l or (r or by_left_rules)
// =R : as the equivalence
with prove ($n +1) $Γ (pEq $x $y) ↪ prove ($n +1) $Γ (pIff $x $y);

rule scan _ _ □ _ ↪ false
// ⊥L
with scan _ _ (pFalse ⸬ _) _ ↪ true
// ⊤L : a trivial hypothesis is dropped
with scan $n $done (pTrue ⸬ $t) $g ↪ prove $n ($done ++ $t) $g
// ∧L
with scan $n $done (pAnd $x $y ⸬ $t) $g ↪
  prove $n ($x ⸬ $y ⸬ ($done ++ $t)) $g
// ∨L : invertible, but branching
with scan $n $done (pOr $x $y ⸬ $t) $g ↪
  let Γ ≔ $done ++ $t in
  let l ≔ prove $n ($x ⸬ Γ) $g in
  let r ≔ prove $n ($y ⸬ Γ) $g in
  l and r
// ⊤⇒ : ⊤ ⇒ C gives C
with scan $n $done (pImpl pTrue $c ⸬ $t) $g ↪ prove $n ($c ⸬ ($done ++ $t)) $g
// ⊥⇒ : ⊥ ⇒ C is useless
with scan $n $done (pImpl pFalse _ ⸬ $t) $g ↪ prove $n ($done ++ $t) $g
// ∧⇒ : currying
with scan $n $done (pImpl (pAnd $x $y) $c ⸬ $t) $g ↪
  prove $n (pImpl $x (pImpl $y $c) ⸬ ($done ++ $t)) $g
// ∨⇒ : splitting
with scan $n $done (pImpl (pOr $x $y) $c ⸬ $t) $g ↪
  prove $n (pImpl $x $c ⸬ pImpl $y $c ⸬ ($done ++ $t)) $g
// atom⇒ : fires only when the antecedent is already known
with scan $n $done (pImpl (pOther $i) $c ⸬ $t) $g ↪
  let Γ ≔ $done ++ $t in
  let antecedent ≔ knows_var $i Γ in
  let consequent ≔ prove $n ($c ⸬ Γ) $g in
  let resume ≔ scan $n (pImpl (pOther $i) $c ⸬ $done) $t $g in
  (antecedent and consequent) or resume
// ⇒⇒ : Dyckhoff's rule, the replacement for contraction on (X ⇒ Y) ⇒ C
with scan $n $done (pImpl (pImpl $x $y) $c ⸬ $t) $g ↪
  let Γ ≔ $done ++ $t in
  let antecedent ≔ prove $n (pImpl $y $c ⸬ Γ) (pImpl $x $y) in
  let consequent ≔ prove $n ($c ⸬ Γ) $g in
  let resume ≔ scan $n (pImpl (pImpl $x $y) $c ⸬ $done) $t $g in
  (antecedent and consequent) or resume
// =L : both implications
with scan $n $done (pEq $x $y ⸬ $t) $g ↪
  prove $n (pImpl $x $y ⸬ pImpl $y $x ⸬ ($done ++ $t)) $g
// =⇒ : currying, as for ∧⇒
with scan $n $done (pImpl (pEq $x $y) $c ⸬ $t) $g ↪
  prove $n (pImpl (pImpl $x $y) (pImpl (pImpl $y $x) $c) ⸬ ($done ++ $t)) $g
// an atomic hypothesis carries no left rule: park it
with scan $n $done (pOther $i ⸬ $t) $g ↪ scan $n (pOther $i ⸬ $done) $t $g;

// Search depth granted to `prove`. Every rule application removes a connective
// from the sequent except ⇒⇒, which duplicates the antecedent of the principal
// implication, so the number of connectives is not a bound: we take its square.
symbol weight : form → ℕ;
rule weight pTrue ↪ _0 +1
with weight pFalse ↪ _0 +1
with weight (pOther _) ↪ _0 +1
with weight (pAnd $x $y) ↪ (weight $x + weight $y) +1
with weight (pOr $x $y) ↪ (weight $x + weight $y) +1
with weight (pImpl $x $y) ↪ (weight $x + weight $y) +1
with weight (pEq $x $y) ↪ weight (pIff $x $y);

symbol fuel (g : form) : ℕ ≔ weight g * weight g;

assert ⊢ prove 20 ((pOther 0) ⸬ □) (pAnd (pOther 0) pTrue) ≡ true;
assertnot ⊢ prove 20 ((pOther 0) ⸬ □) (pAnd (pOther 0) pFalse) ≡ true;
// the left rules LJT adds, on the sequents the previous version could not do
assert ⊢ prove 20 (pOr (pOther 0) (pOther 1) ⸬ □) (pOr (pOther 1) (pOther 0)) ≡ true;
assert ⊢ prove 20 (pImpl (pOther 0) (pOther 1) ⸬ pOther 0 ⸬ □) (pOther 1) ≡ true;
// Peirce's law is classical: it must *not* be found
assertnot ⊢ prove 40 □
  (pImpl (pImpl (pImpl (pOther 0) (pOther 1)) (pOther 0)) (pOther 0)) ≡ true;
// equalities between propositions
assert ⊢ prove 20 □ (pEq (pOr (pOther 0) pFalse) (pOther 0)) ≡ true;
assert ⊢ prove 20 (pEq (pOther 0) (pOther 1) ⸬ pOther 0 ⸬ □) (pOther 1) ≡ true;
assertnot ⊢ prove 20 □ (pEq (pOther 0) (pOther 1)) ≡ true;

///////////////////////////////////////////////////////////////////////////////
// Soundness
///////////////////////////////////////////////////////////////////////////////

opaque symbol is_false_sound (σ: 𝕃 o) (p: form) : π (is_false p) → π (formD σ p) → π ⊥ ≔
begin
    assume σ;
    induction
    { assume h d; apply ⊥ₑ h }
    { assume h d; apply d }
    { assume x ihx y ihy h d; apply ⊥ₑ h }
    { assume x ihx y ihy h d; apply ⊥ₑ h }
    { assume x ihx y ihy h d; apply ⊥ₑ h }
    { assume j h d; apply ⊥ₑ h }
    { assume x ihx y ihy h d; apply ⊥ₑ h }
end;

opaque symbol is_var_sound (σ: 𝕃 o) (i: ℕ) (p: form) : π (is_var i p) → π (formD σ p) → π (nth not_found σ i) ≔
begin
    assume σ i;
    induction
    { assume h d; apply ⊥ₑ h }
    { assume h d; apply ⊥ₑ h }
    { assume x ihx y ihy h d; apply ⊥ₑ h }
    { assume x ihx y ihy h d; apply ⊥ₑ h }
    { assume x ihx y ihy h d; apply ⊥ₑ h }
    { assume j h d; rewrite eqn_correct i j h; apply d }
    { assume x ihx y ihy h d; apply ⊥ₑ h }
end;

// `has f (x ⸬ l)` computes to `if (f x) true (has f l)`.
opaque symbol if_true_or (b q : 𝔹) : π (istrue (@if b bool true q)) → π (istrue b ∨ istrue q) ≔
begin
    assume b q;
    refine ind_𝔹 (λ b, istrue (@if b bool true q) ⇒ (istrue b ∨ istrue q)) _ _ b
    { assume h; refine ∨ᵢ₁ ⊤ᵢ }
    { assume h; refine ∨ᵢ₂ h }
end;

opaque symbol ∨_has [a] (f: τ a → 𝔹) (x: τ a) (l: 𝕃 a) : π (has f (x ⸬ l)) → π (f x ∨ has f l) ≔
begin
    assume a f x l; refine if_true_or (f x) (has f l)
end;

opaque symbol knows_false_sound (σ: 𝕃 o) (c: 𝕃 formS) : π (knows_false c) → π (formD σ (All c)) → π ⊥ ≔
begin
    assume σ;
    induction
    { assume h d; apply h }
    { assume p c ih h d;
      have e: π (is_false p ∨ knows_false c) { refine ∨_has is_false p c h };
      apply ∨ₑ e
      { assume hp; apply is_false_sound σ p hp (∧ₑ₁ d) }
      { assume hc; apply ih hc (∧ₑ₂ d) }
    }
end;

opaque symbol knows_var_sound (σ: 𝕃 o) (i: ℕ) (c: 𝕃 formS) : π (knows_var i c) → π (formD σ (All c)) → π (nth not_found σ i) ≔
begin
    assume σ i;
    induction
    { assume h d; apply ⊥ₑ h }
    { assume p c ih h d;
      have e: π (is_var i p ∨ knows_var i c) { refine ∨_has (is_var i) p c h };
      apply ∨ₑ e
      { assume hp; apply is_var_sound σ i p hp (∧ₑ₁ d) }
      { assume hc; apply ih hc (∧ₑ₂ d) }
    }
end;

// The context of a sequent being scanned is `done ++ (p ⸬ todo)`: singling out
// the hypothesis under focus is the only context surgery the proofs need.
opaque symbol All_split (σ: 𝕃 o) (p: form) (t: 𝕃 formS) :
  Π (done: 𝕃 formS),
    π (formD σ (All (done ++ (p ⸬ t)))) →
    π (formD σ p ∧ formD σ (All (done ++ t))) ≔
begin
  assume σ p t;
  induction
  { assume d; refine ∧ᵢ (∧ₑ₁ d) (∧ₑ₂ d) }
  { assume q done ih d;
    have e: π (formD σ p ∧ formD σ (All (done ++ t))) { refine ih (∧ₑ₂ d) };
    refine ∧ᵢ (∧ₑ₁ e) (∧ᵢ (∧ₑ₁ d) (∧ₑ₂ e))
  }
end;

/* The soundness of the two phases is mutual, and the recursion that ties them
   is the one on the fuel. We break the knot by making the induction hypothesis
   on `prove` an explicit argument of the `scan` lemmas. */

// The ⇒-left rules, one lemma per shape of the antecedent. Only the last one
// is not immediate: it is the semantic content of Dyckhoff's ⇒⇒ rule.
opaque symbol and_imp [X Y C : Prop] : π ((X ∧ Y) ⇒ C) → π (X ⇒ Y ⇒ C) ≔
begin
  assume X Y C h x y; refine h (∧ᵢ x y)
end;

opaque symbol or_imp₁ [X Y C : Prop] : π ((X ∨ Y) ⇒ C) → π (X ⇒ C) ≔
begin
  assume X Y C h x; refine h (∨ᵢ₁ x)
end;

opaque symbol or_imp₂ [X Y C : Prop] : π ((X ∨ Y) ⇒ C) → π (Y ⇒ C) ≔
begin
  assume X Y C h y; refine h (∨ᵢ₂ y)
end;

// An equality between propositions is the conjunction of both implications.
opaque symbol eq_imp₁ [X Y : Prop] : π (X = Y) → π (X ⇒ Y) ≔
begin
  assume X Y e x; rewrite left e; refine x
end;

opaque symbol eq_imp₂ [X Y : Prop] : π (X = Y) → π (Y ⇒ X) ≔
begin
  assume X Y e y; rewrite e; refine y
end;

opaque symbol eq_imp [X Y C : Prop] : π ((X = Y) ⇒ C) → π ((X ⇒ Y) ⇒ (Y ⇒ X) ⇒ C) ≔
begin
  assume X Y C h u v; refine h (propExt X Y u v)
end;

opaque symbol imp_imp_left [X Y C : Prop] :
  π ((X ⇒ Y) ⇒ C) → π ((Y ⇒ C) ⇒ (X ⇒ Y)) → π C ≔
begin
  assume X Y C h k; refine h (k (λ y, h (λ _, y)))
end;

// `scan` on a hypothesis of the form `pImpl x c`, by cases on `x`.
opaque symbol scan_imp_sound (σ: 𝕃 o) (n: ℕ)
  (IH: Π (g: form) (Γ: 𝕃 formS),
         π (prove n Γ g) → π (formD σ (All Γ)) → π (formD σ g))
  (g: form) (t: 𝕃 formS)
  (IHt: Π (done: 𝕃 formS),
          π (scan n done t g) → π (formD σ (All (done ++ t))) → π (formD σ g))
  (c: form) :
  Π (x: form) (done: 𝕃 formS),
    π (scan n done (pImpl x c ⸬ t) g) →
    π (formD σ (All (done ++ (pImpl x c ⸬ t)))) →
    π (formD σ g) ≔
begin
  assume σ n IH g t IHt c;
  induction
  // x = pTrue : ⊤ ⇒ C gives C
  { assume done h d;
    have e: π (formD σ (pImpl pTrue c) ∧ formD σ (All (done ++ t)))
      { refine All_split σ (pImpl pTrue c) t done d };
    refine IH g (c ⸬ (done ++ t)) h (∧ᵢ (∧ₑ₁ e ⊤ᵢ) (∧ₑ₂ e))
  }
  // x = pFalse : the hypothesis is useless
  { assume done h d;
    have e: π (formD σ (pImpl pFalse c) ∧ formD σ (All (done ++ t)))
      { refine All_split σ (pImpl pFalse c) t done d };
    refine IH g (done ++ t) h (∧ₑ₂ e)
  }
  // x = pAnd u v : currying
  { assume u ihu v ihv done h d;
    have e: π (formD σ (pImpl (pAnd u v) c) ∧ formD σ (All (done ++ t)))
      { refine All_split σ (pImpl (pAnd u v) c) t done d };
    refine IH g (pImpl u (pImpl v c) ⸬ (done ++ t)) h
      (∧ᵢ (and_imp (∧ₑ₁ e)) (∧ₑ₂ e))
  }
  // x = pOr u v : splitting
  { assume u ihu v ihv done h d;
    have e: π (formD σ (pImpl (pOr u v) c) ∧ formD σ (All (done ++ t)))
      { refine All_split σ (pImpl (pOr u v) c) t done d };
    refine IH g (pImpl u c ⸬ pImpl v c ⸬ (done ++ t)) h
      (∧ᵢ (or_imp₁ (∧ₑ₁ e)) (∧ᵢ (or_imp₂ (∧ₑ₁ e)) (∧ₑ₂ e)))
  }
  // x = pImpl u v : Dyckhoff's rule
  { assume u ihu v ihv done h d;
    have e: π (formD σ (pImpl (pImpl u v) c) ∧ formD σ (All (done ++ t)))
      { refine All_split σ (pImpl (pImpl u v) c) t done d };
    have s: π ((prove n (pImpl v c ⸬ (done ++ t)) (pImpl u v)
                and prove n (c ⸬ (done ++ t)) g)
               ∨ scan n (pImpl (pImpl u v) c ⸬ done) t g)
      { refine ∨_istrue h };
    apply ∨ₑ s
    { assume hl;
      have p: π (prove n (pImpl v c ⸬ (done ++ t)) (pImpl u v)
                 ∧ prove n (c ⸬ (done ++ t)) g)
        { refine ∧_istrue hl };
      have k: π ((formD σ v ⇒ formD σ c) ⇒ (formD σ u ⇒ formD σ v))
        { assume hv;
          refine IH (pImpl u v) (pImpl v c ⸬ (done ++ t)) (∧ₑ₁ p)
            (∧ᵢ hv (∧ₑ₂ e)) };
      refine IH g (c ⸬ (done ++ t)) (∧ₑ₂ p)
        (∧ᵢ (imp_imp_left (∧ₑ₁ e) k) (∧ₑ₂ e))
    }
    { assume hr;
      refine IHt (pImpl (pImpl u v) c ⸬ done) hr (∧ᵢ (∧ₑ₁ e) (∧ₑ₂ e))
    }
  }
  // x = pOther i : the rule fires only if the atom is known
  { assume i done h d;
    have e: π (formD σ (pImpl (pOther i) c) ∧ formD σ (All (done ++ t)))
      { refine All_split σ (pImpl (pOther i) c) t done d };
    have s: π ((knows_var i (done ++ t) and prove n (c ⸬ (done ++ t)) g)
               ∨ scan n (pImpl (pOther i) c ⸬ done) t g)
      { refine ∨_istrue h };
    apply ∨ₑ s
    { assume hl;
      have p: π (knows_var i (done ++ t) ∧ prove n (c ⸬ (done ++ t)) g)
        { refine ∧_istrue hl };
      have ha: π (nth not_found σ i)
        { refine knows_var_sound σ i (done ++ t) (∧ₑ₁ p) (∧ₑ₂ e) };
      refine IH g (c ⸬ (done ++ t)) (∧ₑ₂ p) (∧ᵢ (∧ₑ₁ e ha) (∧ₑ₂ e))
    }
    { assume hr;
      refine IHt (pImpl (pOther i) c ⸬ done) hr (∧ᵢ (∧ₑ₁ e) (∧ₑ₂ e))
    }
  }
  // x = pEq u v : both implications, curried
  { assume u ihu v ihv done h d;
    have e: π (formD σ (pImpl (pEq u v) c) ∧ formD σ (All (done ++ t)))
      { refine All_split σ (pImpl (pEq u v) c) t done d };
    refine IH g (pImpl (pImpl u v) (pImpl (pImpl v u) c) ⸬ (done ++ t)) h
      (∧ᵢ (eq_imp (∧ₑ₁ e)) (∧ₑ₂ e))
  }
end;

// `scan` on the first hypothesis of `todo`, by cases on it.
opaque symbol scan_cons_sound (σ: 𝕃 o) (n: ℕ)
  (IH: Π (g: form) (Γ: 𝕃 formS),
         π (prove n Γ g) → π (formD σ (All Γ)) → π (formD σ g))
  (g: form) (t: 𝕃 formS)
  (IHt: Π (done: 𝕃 formS),
          π (scan n done t g) → π (formD σ (All (done ++ t))) → π (formD σ g)) :
  Π (p: form) (done: 𝕃 formS),
    π (scan n done (p ⸬ t) g) →
    π (formD σ (All (done ++ (p ⸬ t)))) →
    π (formD σ g) ≔
begin
  assume σ n IH g t IHt;
  induction
  // p = pTrue : dropped
  { assume done h d;
    have e: π (formD σ pTrue ∧ formD σ (All (done ++ t)))
      { refine All_split σ pTrue t done d };
    refine IH g (done ++ t) h (∧ₑ₂ e)
  }
  // p = pFalse : ⊥L closes the branch
  { assume done h d;
    have e: π (formD σ pFalse ∧ formD σ (All (done ++ t)))
      { refine All_split σ pFalse t done d };
    apply ⊥ₑ (∧ₑ₁ e)
  }
  // p = pAnd u v
  { assume u ihu v ihv done h d;
    have e: π (formD σ (pAnd u v) ∧ formD σ (All (done ++ t)))
      { refine All_split σ (pAnd u v) t done d };
    refine IH g (u ⸬ v ⸬ (done ++ t)) h
      (∧ᵢ (∧ₑ₁ (∧ₑ₁ e)) (∧ᵢ (∧ₑ₂ (∧ₑ₁ e)) (∧ₑ₂ e)))
  }
  // p = pOr u v : both branches must succeed
  { assume u ihu v ihv done h d;
    have e: π (formD σ (pOr u v) ∧ formD σ (All (done ++ t)))
      { refine All_split σ (pOr u v) t done d };
    have p: π (prove n (u ⸬ (done ++ t)) g ∧ prove n (v ⸬ (done ++ t)) g)
      { refine ∧_istrue h };
    apply ∨ₑ (∧ₑ₁ e)
    { assume hu; refine IH g (u ⸬ (done ++ t)) (∧ₑ₁ p) (∧ᵢ hu (∧ₑ₂ e)) }
    { assume hv; refine IH g (v ⸬ (done ++ t)) (∧ₑ₂ p) (∧ᵢ hv (∧ₑ₂ e)) }
  }
  // p = pImpl u v : delegated
  { assume u ihu v ihv done h d;
    refine scan_imp_sound σ n IH g t IHt v u done h d
  }
  // p = pOther i : parked
  { assume i done h d;
    have e: π (formD σ (pOther i) ∧ formD σ (All (done ++ t)))
      { refine All_split σ (pOther i) t done d };
    refine IHt (pOther i ⸬ done) h (∧ᵢ (∧ₑ₁ e) (∧ₑ₂ e))
  }
  // p = pEq u v : both implications
  { assume u ihu v ihv done h d;
    have e: π (formD σ (pEq u v) ∧ formD σ (All (done ++ t)))
      { refine All_split σ (pEq u v) t done d };
    refine IH g (pImpl u v ⸬ pImpl v u ⸬ (done ++ t)) h
      (∧ᵢ (eq_imp₁ (∧ₑ₁ e)) (∧ᵢ (eq_imp₂ (∧ₑ₁ e)) (∧ₑ₂ e)))
  }
end;

// The left phase, by induction on the hypotheses still to visit.
opaque symbol scan_sound (σ: 𝕃 o) (n: ℕ)
  (IH: Π (g: form) (Γ: 𝕃 formS),
         π (prove n Γ g) → π (formD σ (All Γ)) → π (formD σ g))
  (g: form) :
  Π (todo done: 𝕃 formS),
    π (scan n done todo g) →
    π (formD σ (All (done ++ todo))) →
    π (formD σ g) ≔
begin
  assume σ n IH g;
  induction
  { assume done h d; apply ⊥ₑ h }
  { assume p t IHt done h d;
    refine scan_cons_sound σ n IH g t IHt p done h d
  }
end;

// The right phase, by induction on the fuel.
opaque symbol prove_sound (σ: 𝕃 o) :
  Π (n: ℕ) (g: form) (Γ: 𝕃 formS),
    π (prove n Γ g) → π (formD σ (All Γ)) → π (formD σ g) ≔
begin
  assume σ;
  induction
  // no fuel left
  { assume g Γ h d; apply ⊥ₑ h }
  { assume n IH;
    induction
    // ⊤R
    { assume Γ h d; apply ⊤ᵢ }
    // ⊥ goal: ⊥L or the left rules
    { assume Γ h d;
      have s: π (knows_false Γ ∨ scan n □ Γ pFalse) { refine ∨_istrue h };
      apply ∨ₑ s
      { assume hl; apply knows_false_sound σ Γ hl d }
      { assume hr; refine scan_sound σ n IH pFalse Γ □ hr d }
    }
    // ∧R
    { assume x ihx y ihy Γ h d;
      have p: π (prove n Γ x ∧ prove n Γ y) { refine ∧_istrue h };
      refine ∧ᵢ (IH x Γ (∧ₑ₁ p) d) (IH y Γ (∧ₑ₂ p) d)
    }
    // ∨R, then the left rules
    { assume x ihx y ihy Γ h d;
      have s: π (prove n Γ x ∨ (prove n Γ y or scan n □ Γ (pOr x y)))
        { refine ∨_istrue h };
      apply ∨ₑ s
      { assume hx; apply ∨ᵢ₁; refine IH x Γ hx d }
      { assume h2;
        have s2: π (prove n Γ y ∨ scan n □ Γ (pOr x y)) { refine ∨_istrue h2 };
        apply ∨ₑ s2
        { assume hy; apply ∨ᵢ₂; refine IH y Γ hy d }
        { assume hs; refine scan_sound σ n IH (pOr x y) Γ □ hs d }
      }
    }
    // ⇒R
    { assume x ihx y ihy Γ h d;
      assume hx; refine IH y (x ⸬ Γ) h (∧ᵢ hx d)
    }
    // atomic goal: axiom or the left rules
    { assume i Γ h d;
      have s: π (knows_var i Γ ∨ scan n □ Γ (pOther i)) { refine ∨_istrue h };
      apply ∨ₑ s
      { assume hl; apply knows_var_sound σ i Γ hl d }
      { assume hr; refine scan_sound σ n IH (pOther i) Γ □ hr d }
    }
    // =R : both implications, then propositional extensionality
    { assume x ihx y ihy Γ h d;
      have p: π (prove n Γ (pImpl x y) ∧ prove n Γ (pImpl y x)) { refine ∧_istrue h };
      refine propExt (formD σ x) (formD σ y)
        (IH (pImpl x y) Γ (∧ₑ₁ p) d) (IH (pImpl y x) Γ (∧ₑ₂ p) d)
    }
  }
end;

///////////////////////////////////////////////////////////////////////////////
// Reification
///////////////////////////////////////////////////////////////////////////////

// Atoms are looked up with core's `index`, which compares them up to conversion.
// (Stdlib.List has an `index` too.)

protected sequential symbol formReify: (𝕃 o) →  Prop → τ (formS × (list o));
rule formReify $ctx ⊤ ↪ (pTrue ‚ $ctx)
with formReify $ctx ⊥ ↪ (pFalse ‚ $ctx)
with formReify $ctx ($x ∧ $y) ↪ let res1 ≔  (formReify $ctx $x) in
                                let res2 ≔  (formReify (res1 ₂) $y) in
                                (pAnd (res1 ₁) (res2 ₁) ‚ (res2 ₂))
with formReify $ctx ($x ∨ $y) ↪ let res1 ≔  (formReify $ctx $x) in
                                let res2 ≔  (formReify (res1 ₂) $y) in
                                (pOr (res1 ₁) (res2 ₁) ‚ (res2 ₂))
with formReify $ctx ($x ⇒ ⊥) ↪ let res ≔  (formReify $ctx $x) in
                                (pNot (res ₁)‚ (res ₂))
with formReify $ctx ($x ⇒ $y) ↪ let res1 ≔  (formReify $ctx $x) in
                                let res2 ≔  (formReify (res1 ₂) $y) in
                                (pImpl (res1 ₁) (res2 ₁) ‚ (res2 ₂))
with formReify $ctx ($x ⇔ $y) ↪ let res1 ≔  (formReify $ctx $x) in
                                let res2 ≔  (formReify (res1 ₂) $y) in
                                (pIff (res1 ₁) (res2 ₁) ‚ (res2 ₂))
with formReify $ctx (@= o $x $y) ↪ let res1 ≔  (formReify $ctx $x) in
                                let res2 ≔  (formReify (res1 ₂) $y) in
                                (pEq (res1 ₁) (res2 ₁) ‚ (res2 ₂))
with formReify $ctx $x ↪
    alethe.core.case (alethe.core.index _0 $x $ctx) (λ i, pOther i ‚ $ctx) (λ i, pOther i ‚ ($ctx ++ ($x ⸬ □)));

protected symbol form_reify goal ≔ formReify □ goal;

symbol tauto_aux [goal] ≔
  let res ≔ form_reify goal in prove_sound (res ₂) (fuel (res ₁)) (res ₁) □;

symbol #tauto ≔ #refine "(tauto_aux ⊤ᵢ ⊤ᵢ)";

// Classical: the double negation of a classical tautology is intuitionistic.
symbol #cauto ≔ #refine "¬¬ₑ _ (tauto_aux ⊤ᵢ ⊤ᵢ)";

///////////////////////////////////////////////////////////////////////////////
// Examples
///////////////////////////////////////////////////////////////////////////////

// Purely propositional goal
private symbol example_prop (a b c d e g : Prop) :
  π ((a ∧ b) ∧ (c ∧ ⊤) ∧ d
     ⇒ (d ∧ (c ∧ a)) ∧ (e ∨ (g ∨ b)) ∧ (e ∧ g ⇒ (g ∧ b) ∧ (⊥ ∨ e))) ≔
begin assume a b c d e g; eval #tauto; end;

// Non-propositional formulas are abstracted as atoms, identified up to conversion.
private symbol example_atoms (x y z : ℕ) (p : ℕ → Prop) :
  π ((x ≤ y ∧ 2 + 1 ≤ z) ∧ (`∀ n, p n) ∧ x + y = z
     ⇒ ((x = z ∨ x + y = z) ∧ 3 ≤ z) ∧ ((`∃ n, p n) ⇒ (`∀ n, p n) ∧ x ≤ y)) ≔
begin assume x y z p; eval #tauto; end;

// The left rules: none of these were provable before.
private symbol example_or_left (a b : Prop) : π (a ∨ b ⇒ b ∨ a) ≔
begin assume a b; eval #tauto; end;

private symbol example_modus_ponens (a b : Prop) : π ((a ⇒ b) ⇒ a ⇒ b) ≔
begin assume a b; eval #tauto; end;

private symbol example_chain (a b c : Prop) :
  π ((a ⇒ b) ∧ (b ⇒ c) ⇒ a ⇒ c) ≔
begin assume a b c; eval #tauto; end;

private symbol example_curry (a b c : Prop) :
  π ((a ∧ b ⇒ c) ⇒ a ⇒ b ⇒ c) ≔
begin assume a b c; eval #tauto; end;

private symbol example_distrib (a b c : Prop) :
  π (a ∧ (b ∨ c) ⇔ (a ∧ b) ∨ (a ∧ c)) ≔
begin assume a b c; eval #tauto; end;

private symbol example_contrapos (a b : Prop) :
  π ((a ⇒ b) ⇒ ¬ b ⇒ ¬ a) ≔
begin assume a b; eval #tauto; end;

// Dyckhoff's ⇒⇒ rule is what makes this one terminate without loop-checking.
private symbol example_imp_imp (a b : Prop) :
  π (((a ⇒ b) ⇒ a) ⇒ (a ⇒ b) ⇒ b) ≔
begin assume a b; eval #tauto; end;

// Equalities between propositions, and classical goals, from Alethe steps.
private symbol U : Set;
private symbol f1 : τ U;
private symbol f2 : τ U;

// aci_simp: `(= (or (= f1 f2) false) (= f1 f2))`
private symbol example_aci_simp : π (((f1 = f2) ∨ ⊥) = (f1 = f2)) ≔
begin eval #tauto; end;

// aci_simp: `(= p (or p p))`, in an Alethe clause
private symbol example_aci_simp_dup (q : Prop) : alethe.core.π̇ ((q = (q ∨ q)) ⸬ □) ≔
begin assume q; eval #tauto; end;

// ac_simp then and_simplify: `(and false false q)` is `false`
private symbol example_and_simplify (q : Prop) :
  alethe.core.π̇ (((⊥ ∧ ⊥ ∧ q) = (⊥ ∧ q)) ⸬ ((⊥ ∧ q) = ⊥) ⸬ □) ≔
begin assume q; eval #tauto; end;

// equalities nested in equalities
private symbol example_eq_eq (a b : Prop) : π ((a = b) = (b = a)) ≔
begin assume a b; eval #tauto; end;

// and_pos and implies_neg1 are only classically valid as disjunctions
private symbol example_and_pos (a b : Prop) : alethe.core.π̇ ((¬ (a ∧ b)) ⸬ a ⸬ □) ≔
begin assume a b; eval #cauto; end;

private symbol example_implies_neg1 (a b : Prop) : alethe.core.π̇ ((a ⇒ b) ⸬ a ⸬ □) ≔
begin assume a b; eval #cauto; end;

// bool_simplify: `((a ⇒ b) ⇒ b) = (a ∨ b)`, and not_simplify: `¬¬a = a`
private symbol example_bool_simplify (a b : Prop) : π (((a ⇒ b) ⇒ b) = (a ∨ b)) ≔
begin assume a b; eval #cauto; end;

private symbol example_not_not (a : Prop) : π ((¬ ¬ a) = a) ≔
begin assume a; eval #cauto; end;

// not_xor1: from `¬ (xor a b)`, the clause `a ∨ ¬ b`
private symbol example_not_xor1 (a b : Prop) :
  π (¬ (((¬ a) ∧ b) ∨ (a ∧ (¬ b))) ⇒ alethe.core.disj (a ⸬ (¬ b) ⸬ □)) ≔
begin assume a b; eval #cauto; end;
