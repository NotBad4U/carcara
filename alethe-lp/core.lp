// The Alethe calculus: the encoding, the clause type and its proof judgement,
// the classical and propositional toolbox, congruence, resolution and the
// list-clause machinery. Required by every generated proof, whatever the logic.
//
// Numerals are bound to ℕ here because the clause indices are natural numbers.
// The arithmetic layers (alethe.lia, alethe.lra) rebind them to their own
// carrier and are always opened after this module.
require open Stdlib.HOL Stdlib.ExtraRules Stdlib.Bool Stdlib.Nat Stdlib.PropExt;
require open Stdlib.List Stdlib.Comp;
require open Stdlib.String Stdlib.Univ Stdlib.Tactic;
builtin "0" ≔ Stdlib.Nat._0;
builtin "1" ≔ Stdlib.Nat._1;
builtin "2" ≔ Stdlib.Nat._2;
builtin "3" ≔ Stdlib.Nat._3;
builtin "4" ≔ Stdlib.Nat._4;
builtin "5" ≔ Stdlib.Nat._5;
builtin "6" ≔ Stdlib.Nat._6;
builtin "7" ≔ Stdlib.Nat._7;
builtin "8" ≔ Stdlib.Nat._8;
builtin "9" ≔ Stdlib.Nat._9;
builtin "10" ≔ Stdlib.Nat._10;
builtin "+" ≔ Stdlib.Nat.+;
builtin "*" ≔ Stdlib.Nat.*;

notation ¬ prefix 35;

// testing symbols
private symbol a: Prop;
private symbol b: Prop;
private symbol c: Prop;
private symbol d: Prop;
private symbol e: Prop;

symbol Bool ≔ o;

// A clause is a list of propositions -- the Stdlib `𝕃 o`, with `□` for the
// empty clause and `⸬` for the literal cons -- and `disj` reads one back as a
// disjunction. `π̇ l` is the judgement "the clause `l` holds".
//
// `disj` is declared here rather than reused from `Stdlib.Disj`, whose version
// carries a third rule `disj ($l ⸬ □) ↪ $l` that drops the trailing `⊥`. The
// `or_identity_r` / `#repeat_or_id_r` machinery below -- and the
// `eval #repeat_or_id_r` the translator emits -- exists precisely because our
// `disj` keeps that `⊥`. Opening `Stdlib.Disj` would silently install the other
// one and break every one of those rewrites.
symbol disj : 𝕃 o → τ o;
rule disj ($l1 ⸬ $l) ↪ ($l1 ∨ disj $l)
with disj □ ↪ ⊥;

opaque symbol disj_cat (l l' : 𝕃 o) : π (disj (l ++ l') = (disj l ∨ disj l')) ≔
begin
  induction
  { assume l'; simplify; rewrite ⊥∨; reflexivity }
  { assume l0 l ih l'; simplify; rewrite ih l'; rewrite ∨_assoc; reflexivity }
end;

// Flattens an `∨`-chain into the clause it denotes. Used by the `or` rule.
sequential symbol ∨_to_list: Prop → 𝕃 o;
rule ∨_to_list ($x ∨ $y) ↪ $x ⸬ (∨_to_list $y)
with ∨_to_list ⊥ ↪ □;

assert ⊢ disj (a ⸬ b ⸬ □) ≡ a ∨ b ∨ ⊥;
assert ⊢ ∨_to_list (a ∨ b ∨ ⊥ ∨ c ∨ ⊥) ≡ (a ⸬ b ⸬ ⊥ ⸬ c ⸬ □);

injective symbol π̇ (l : 𝕃 o) : TYPE ≔ π (disj l);

opaque symbol π̇ₗ [a] : π̇ (a ⸬ □)  → π a ≔
begin
  assume a Hcl_a;
  apply @∨ₑ a ⊥ a
  { apply Hcl_a }
  { assume Ha; apply Ha }
  { assume False; apply ⊥ₑ False; };
end;

// opaque injective symbol π p : TYPE ≔ π (¬ (¬ p));

// Introduction rule for clauses
// construct `p ⸬ q` from a clause with only `p`
opaque symbol ⟇ᵢ₁ [p q] : π̇ (p ⸬ □) → π̇ (p ⸬ q) ≔
begin
  assume p q Hp;
  apply ∨ₑ Hp
  { assume Hpi_p; apply ∨ᵢ₁;  apply Hpi_p }
  { assume Hbot; apply ⊥ₑ; apply Hbot }
end;

// construct `p ⸬ q` from a proof of `p`
opaque symbol ⟇ᵢ₁' [p q] : π p → π̇ (p ⸬ q) ≔
begin
  assume p q Hp; apply ∨ᵢ₁; apply Hp
end;

opaque symbol ⟇ᵢ₂ [p q] : π̇ q → π̇ (p ⸬ q) ≔
begin
  assume p q Hq; apply ∨ᵢ₂; apply Hq
end;

// Elimination rule for clause
opaque symbol ⟇ₑ [p q r] : π̇ (p ⸬ q) → (π̇ (p ⸬ □) → π̇ r) → (π̇ q → π̇ r) → π̇ r ≔
begin
  assume p q r Hpq Hpr Hqr;
  apply ∨ₑ Hpq
  { assume Hp; apply Hpr (∨ᵢ₁ Hp) }
  { assume Hq; apply Hqr Hq }
end;


constant symbol nnpp_eq p : π ((¬ ¬ p) = p);

// Axiom propositional_extensionality: forall (P Q : Prop), (P <-> Q) -> P = Q.
// τ o ↪ Prop
constant symbol prop_ext [p: Prop] [q: Prop]: π (p ⇔ q) → π (p = q);

opaque symbol ⟺_ext [p: Prop] [q: Prop]:  π (p = q) → π (p ⇔ q) ≔
begin
  assume p q Heq;  rewrite Heq; apply ⇔_refl
end;

opaque symbol iff_equiv_eq p q: π ((p ⇔ q) = (p = q)) ≔
begin
  assume p q;
  apply prop_ext;
  apply ∧ᵢ
  { assume Hiff; apply prop_ext Hiff }
  { assume Heq; rewrite Heq; apply ⇔_refl }
end;

opaque symbol morgan1 p q : π (¬ (p ∧ q) = (¬ p ∨ ¬ q)) ≔
begin
  assume p q;
  apply prop_ext;
  apply ∧ᵢ
  {
    assume H;
    apply  not_and_or H
  }
  {
    assume H;
    refine or_not_and H
  }
end;

opaque symbol morgan2 p q : π (¬ (p ∨ q) = (¬ p ∧ ¬ q)) ≔
begin
  assume p q;
  apply prop_ext;
  apply ∧ᵢ
  {
    assume H;
    refine not_or_and H
  }
  {
    assume H;
    refine and_not_or H
  }
end;

opaque symbol distributive_or p q r : π ((p ∨ (q ∧ r)) = ((p ∨ q) ∧ (p ∨ r))) ≔
begin
  assume p q r;
  apply prop_ext;
  apply ∧ᵢ
  {
    assume H;
    apply ∧ᵢ
    {
      apply ∨ₑ H
      { assume Hp; apply ∨ᵢ₁; refine Hp }
      { assume Hqr; apply ∨ᵢ₂; refine ∧ₑ₁ Hqr }
    }
    {
      apply ∨ₑ H
      { assume Hp; apply ∨ᵢ₁; refine Hp }
      { assume Hqr; apply ∨ᵢ₂; refine ∧ₑ₂ Hqr }
    }
  }
  {
    assume H;
    have H1: π (p ∨ q) { apply ∧ₑ₁ H  };
    have H2: π (p ∨ r) { apply ∧ₑ₂ H  };
    apply ∨ₑ H1
    {
        assume Hp;
        apply ∨ₑ H2
        {
          assume Hp';
          apply ∨ᵢ₁;
          apply Hp';
        }
        {
          assume Hr;
          apply ∨ᵢ₁;
          apply Hp;
        }
    }
    {
      assume Hq;
      apply ∨ₑ H2
        {
          assume Hp';
          apply ∨ᵢ₁;
          apply Hp';
        }
        {
          assume Hr;
          apply ∨ᵢ₂;
          apply ∧ᵢ
          { refine Hq }
          { refine Hr }
        }
    };
  }
end;

opaque symbol distributive_and p q r : π ((p ∧ (q ∨ r)) = ((p ∧ q) ∨ (p ∧ r))) ≔
begin
  assume p q r;
  apply prop_ext;
  apply ∧ᵢ
  {
    assume H;
    have Hp: π p { apply ∧ₑ₁ H };
    have Hqorr: π (q ∨ r) { apply ∧ₑ₂ H };
    apply ∨ₑ Hqorr
    {
      assume Hq;
      apply ∨ᵢ₁;
      apply ∧ᵢ { refine Hp } { refine Hq }
    }
    {
      assume Hr;
      apply ∨ᵢ₂;
      apply ∧ᵢ { refine Hp } { refine Hr  }
    }
  }
  {
    assume H;
    apply ∨ₑ H
    {
      assume Hpandq;
      apply ∧ᵢ { refine ∧ₑ₁ Hpandq  } { apply ∨ᵢ₁; refine ∧ₑ₂ Hpandq }
    }
    {
      assume Hpandr;
      apply ∧ᵢ { refine ∧ₑ₁ Hpandr  } { apply ∨ᵢ₂; refine ∧ₑ₂ Hpandr }
    }
  }
end;

opaque symbol or_idempotent p : π ((p ∨ p) = p) ≔
begin
  assume p;
  apply prop_ext;
  apply ∧ᵢ
  {
    assume Hporp;
    apply ∨ₑ Hporp
    { assume Hp; refine Hp }
    { assume Hp; refine Hp }
  }
  {
    assume Hp;
    apply ∨ᵢ₁;
    refine Hp
  }
end;

opaque symbol and_idempotent p : π ((p ∧ p) = p) ≔
begin
  assume p;
  apply prop_ext;
  apply ∧ᵢ
  { assume Hpandp; apply ∧ₑ₁ Hpandp; }
  {
    assume Hp;
    apply ∧ᵢ { refine Hp } { refine Hp }
  }
end;

opaque symbol imp_eq_or p q: π (((¬ p) ∨ q) =  (p ⇒ q)) ≔
begin
  assume p q;
  apply prop_ext;
  apply ∧ᵢ
  { assume Hor; refine or_to_imply Hor;  }
  { assume Himp; apply imply_to_or Himp }
end;

opaque symbol contrapos [p q] : π ((p ⇒ q)  ⇔ (¬ q ⇒ ¬ p)) ≔
begin

  assume p q;
  apply ∧ᵢ
  {
    assume Himp;
    assume Hnq;
    assume Hp;
    have Hq: π q
    {  apply Himp Hp };
    apply ¬ₑ Hnq Hq
  }
  {
    assume Himp;
    assume Hp;
    have Hor: π ((¬ ¬ q) ∨ ¬ p) {
      rewrite imp_eq_or;
      refine Himp
    };
    apply ∨ₑ Hor
    { assume Hnnq; rewrite left  nnpp_eq; refine Hnnq }
    { assume Hnp; apply  ¬ₑ Hnp Hp }
  };
end;

// Alias name for `¬¬ₑ`
opaque symbol contradiction p : (π (¬ p) → π ⊥) → π p ≔
begin
  assume p Hnp;
  refine ¬¬ₑ p Hnp
end;

// // Hilbert epsilon operator/choice
opaque  symbol and_identity_r x : π ((x ∧ ⊤) = x) ≔
begin
  assume x;
  apply prop_ext;
  apply ∧ᵢ
  { assume Hand; apply ∧ₑ₁ Hand  }
  { assume Hx; apply ∧ᵢ { refine Hx } { refine ⊤ᵢ } }
end;

opaque  symbol and_identity_l x : π ((⊤ ∧ x) = x) ≔
begin
  assume x;
  apply prop_ext;
  apply ∧ᵢ
  { assume Hand; apply ∧ₑ₂ Hand  }
  { assume Hx; apply ∧ᵢ { refine ⊤ᵢ } { refine Hx } }
end;

opaque  symbol and_domination x : π ((x ∧ ⊥) = ⊥) ≔
begin
  assume x;
  apply prop_ext;
  apply ∧ᵢ
  {  assume Hand; apply ∧ₑ₂ Hand  }
  {  assume Hx; apply ⊥ₑ Hx }
end;

opaque  symbol or_identity_l x : π ((⊥ ∨ x) = x) ≔
begin
  assume x;
  apply prop_ext;
  apply ∧ᵢ
  {  assume Hor; apply ∨ₑ Hor { assume Hbot; apply ⊥ₑ; refine Hbot } { assume Hx; refine Hx }  }
  {  assume Hx; apply ∨ᵢ₂; refine Hx }
end;

opaque  symbol or_identity_r x : π ((x ∨ ⊥) = x) ≔
begin
  assume x;
  apply prop_ext;
  apply ∧ᵢ
  {  assume Hor; apply ∨ₑ Hor { assume Hx; refine Hx } { assume Hbot; apply ⊥ₑ; refine Hbot } }
  {  assume Hx; apply ∨ᵢ₁; refine Hx }
end;

constant symbol ite [a] (c: τ o) (t e: τ a): τ a;

constant symbol ite_ind [a] : Π (c: τ o) (t e: τ a) p,
  (π c → π (p t))
  → ((π c → π ⊥) → π (p e))
  → π (p (@ite a c t e));

compute ite true true false;


opaque symbol cong6 [a1 a2 a3 a4 a5 a6 a7] (f : τ a1 → τ a2 → τ a3 → τ a4 → τ a5 → τ a6 → τ a7):
  Π [x1 x1':τ a1], π (x1 = x1') →
  Π [x2 x2':τ a2], π (x2 = x2') →
  Π [x3 x3':τ a3], π (x3 = x3') →
  Π [x4 x4':τ a4], π (x4 = x4') →
  Π [x5 x5':τ a5], π (x5 = x5') →
  Π [x6 x6':τ a6], π (x6 = x6') →
  π (f x1 x2 x3 x4 x5 x6 = f x1' x2' x3' x4' x5' x6') ≔
begin
  assume a1 a2 a3 a4 a5 a6 a7 f;
  assume x1 x1' H1;
  assume x2 x2' H2;
  assume x3 x3' H3;
  assume x4 x4' H4;
  assume x5 x5' H5;
  assume x6 x6' H6;
  rewrite H1;
  rewrite H2;
  rewrite H3;
  rewrite H4;
  rewrite H5;
  rewrite H6;
  reflexivity
end;

opaque symbol cong7 [a1 a2 a3 a4 a5 a6 a7 a8] (f : τ a1 → τ a2 → τ a3 → τ a4 → τ a5 → τ a6 → τ a7 → τ a8):
  Π [x1 x1':τ a1], π (x1 = x1') →
  Π [x2 x2':τ a2], π (x2 = x2') →
  Π [x3 x3':τ a3], π (x3 = x3') →
  Π [x4 x4':τ a4], π (x4 = x4') →
  Π [x5 x5':τ a5], π (x5 = x5') →
  Π [x6 x6':τ a6], π (x6 = x6') →
  Π [x7 x7':τ a7], π (x7 = x7') →
  π (f x1 x2 x3 x4 x5 x6 x7 = f x1' x2' x3' x4' x5' x6' x7') ≔
begin
  assume a1 a2 a3 a4 a5 a6 a7 a8 f;
  assume x1 x1' H1;
  assume x2 x2' H2;
  assume x3 x3' H3;
  assume x4 x4' H4;
  assume x5 x5' H5;
  assume x6 x6' H6;
  assume x7 x7' H7;
  rewrite H1;
  rewrite H2;
  rewrite H3;
  rewrite H4;
  rewrite H5;
  rewrite H6;
  rewrite H7;
  reflexivity
end;

opaque symbol cong8 [a1 a2 a3 a4 a5 a6 a7 a8 a9] (f : τ a1 → τ a2 → τ a3 → τ a4 → τ a5 → τ a6 → τ a7 → τ a8 → τ a9):
  Π [x1 x1':τ a1], π (x1 = x1') →
  Π [x2 x2':τ a2], π (x2 = x2') →
  Π [x3 x3':τ a3], π (x3 = x3') →
  Π [x4 x4':τ a4], π (x4 = x4') →
  Π [x5 x5':τ a5], π (x5 = x5') →
  Π [x6 x6':τ a6], π (x6 = x6') →
  Π [x7 x7':τ a7], π (x7 = x7') →
  Π [x8 x8':τ a8], π (x8 = x8') →
  π (f x1 x2 x3 x4 x5 x6 x7 x8 = f x1' x2' x3' x4' x5' x6' x7' x8') ≔
begin
  assume a1 a2 a3 a4 a5 a6 a7 a8 a9 f;
  assume x1 x1' H1;
  assume x2 x2' H2;
  assume x3 x3' H3;
  assume x4 x4' H4;
  assume x5 x5' H5;
  assume x6 x6' H6;
  assume x7 x7' H7;
  assume x8 x8' H8;
  rewrite H1;
  rewrite H2;
  rewrite H3;
  rewrite H4;
  rewrite H5;
  rewrite H6;
  rewrite H7;
  rewrite H8;
  reflexivity
end;

opaque symbol negdef p : π ((p ⇒ ⊥) = ¬ p) ≔
begin
  simplify; reflexivity
end;

opaque symbol ite_cong [a] [c c': τ o] [t t' e e': τ a] : π (c = c') → π (t = t') → π (e = e') → π̇ ((ite c t e = ite c' t' e') ⸬ □) ≔
begin
  assume a c c' t t' e e' Hcc' Htt' Hee';
  simplify;
  rewrite or_identity_r;
  rewrite Hcc';
  rewrite Htt';
  rewrite Hee';
  reflexivity
end;

opaque symbol not_not x : π̇ ( (¬ (¬ (¬ x))) ⸬ x ⸬ □) ≔
begin
  assume x;
  apply imply_to_or;
  assume H;
  apply ∨ᵢ₁; 
  refine ¬¬ₑ x H
end;

opaque symbol not_symm [a] [x y: τ a] : π (¬ (x = y) ⇒ (¬ (y = x))) ≔
begin
  assume a x y H;
  assume H2;
  apply H;
  symmetry;
  apply H2
end;

symbol trans [U] [a b c: τ U]: π̇ ((a = b) ⸬ □) → π̇ ((b = c) ⸬ □) → π̇ ((a = c) ⸬ □) ≔
begin
  assume U a b c H1 H2;
  apply ∨ᵢ₁;
  have H2': π (b = c) { apply π̇ₗ H2 };
  have H1': π (a = b) { apply π̇ₗ H1 };
  rewrite H1';
  apply H2'
end;

opaque symbol subproof [φ₁ ψ] : π φ₁ → π ψ → π̇ ((¬ φ₁) ⸬ ψ ⸬ □) ≔
begin
  assume φ₁ ψ Hφ₁ Hψ;
  apply ∨ᵢ₂;
  apply ∨ᵢ₁;
  apply Hψ
end;

symbol Arity (a b: Set): τ nat → Set;
rule Arity $a $b 0 ↪ $b
with Arity $a $b ($n +1) ↪ $a ⤳ (Arity $a $b $n);

// # In Predicate
//
// The In predicate works with 𝔹 instead of Prop to avoid making critical pairs wiht other rules.
// If we use Prop, then we will need a rule
// ▷ `$x ⇔ $x ↪ ⊤` to replace `eq $x $h` and,
// ▷ `_ ∨ ⊤ ↪ ⊤` for `or _ true ↪ true`.
//
// This choice will create a critical pair reduction which would make any clause in the goal
// that contain the litteral ⊤ unable to compute the predicate In.
//
// To illustrate this case, consider the goal:
// ⊢ (𝜑1 ∨ ⋯ ∨ ⊤ ⋯ ∨ 𝜑𝑛), ¬𝜑k
// then we will have
// ⊢ In_∨ 𝜑k (𝜑1 ∨ ⋯ ∨ ⊤ ⋯ ∨ 𝜑𝑛)  (apply or_neg)
// ⊢ In_∨ 𝜑k ⊤  (by simplification)
// we got stuck...

// Decidable equality in 𝔹.
// Symbol = has been declared constant, it cannot be used as the head of a rewrite rule LHS.
// So we create our own eq symbol.


opaque symbol resolutionₗ (x : τ o) (a b : 𝕃 o) : π̇ (x ⸬ a) → π̇ ((¬ x) ⸬ b) → π̇ (a ++ b) ≔
begin
  assume x a b H1 H2;
  simplify; rewrite disj_cat;
  apply ∨ₑ H1
  { assume Hx; apply ∨ᵢ₂;
    apply ∨ₑ H2 { assume Hnx; apply ⊥ₑ (Hnx Hx) } { assume Hb; apply Hb } }
  { assume Ha; apply ∨ᵢ₁; apply Ha }
end;

opaque symbol resolutionᵣ (x : τ o) (a b : 𝕃 o) : π̇ ((¬ x) ⸬ a) → π̇ (x ⸬ b) → π̇ (a ++ b) ≔
begin
  assume x a b H1 H2;
  simplify; rewrite disj_cat;
  apply ∨ₑ H1
  { assume Hnx; apply ∨ᵢ₂;
    apply ∨ₑ H2 { assume Hx; apply ⊥ₑ (Hnx Hx) } { assume Hb; apply Hb } }
  { assume Ha; apply ∨ᵢ₁; apply Ha }
end;

(a: Set) inductive Vec: ℕ → TYPE ≔
| ⧈ : Vec a 0 // \Box
| cons [n: ℕ] : τ a →  Vec a n  →  Vec a (n + 1);

print Vec;

constant symbol vec : Set → ℕ → Set;
rule τ (vec $a $n) ↪ Vec $a $n;

symbol distinct [a] [n: τ nat]  : Vec a n → Prop;

// // boolean case
rule distinct (cons _ ⧈) ↪ ⊤
with distinct (cons $x (cons $y ⧈)) ↪ ($x ≠ $y)
with distinct ⧈ ↪ ⊥
with distinct (cons _ (cons _ (cons _ _))) ↪ ⊥;


// 
assert ⊢ distinct (cons a ⧈) ≡ ⊤;
assert ⊢ distinct ((cons a (cons b ⧈))) ≡ (a ≠ b);
assert ⊢ distinct (cons a (cons b (cons c ⧈))) ≡ ⊥;
assert ⊢ distinct (cons a (cons b (cons c (cons d ⧈)))) ≡ ⊥;


assert ⊢ distinct (cons 1 ⧈) ≡ ⊤;
assert ⊢ distinct ((cons 1 (cons 2 ⧈))) ≡ (1 ≠ 2);
assert ⊢ distinct (cons 1 (cons 2 (cons 3 ⧈))) ≡ ⊥;

opaque symbol distinct_elim  [a] [t: τ a] : π (distinct (cons t ⧈) = ⊤) ≔ eq_refl (distinct(cons t ⧈));

opaque symbol distinct_elim₂ [a] [x y: τ a] : π ((distinct ((cons x (cons y ⧈)))) = (x ≠ y)) ≔ eq_refl (distinct (cons x (cons y ⧈)));

//opaque symbol distinct_elim₃ [a] [n: τ nat] [v: Vec a (n + 3)] : π (distinct v = ⊥) ≔  eq_refl (distinct v);

opaque symbol feq [a b] (f:τ a → τ b) [x x':τ a] : π(x = x') → π(f x = f x') ≔
begin
  assume a b f x x' xx'; rewrite xx'; reflexivity;
end;

opaque symbol feq2 [a b c] (f:τ a → τ b → τ c):
  Π [x x':τ a], π(x = x') → Π [y y':τ b], π(y = y') → π(f x y = f x' y') ≔
begin
  assume a b c f x x' xx' y y' yy'; rewrite xx'; rewrite yy'; reflexivity
end;

opaque symbol feq3 [a b c d] (f:τ a → τ b →  τ c → τ d):
  Π [x x':τ a], π(x = x') → Π [y y':τ b], π(y = y') → Π [z z':τ c], π(z = z') → π(f x y z = f x' y' z') ≔
begin
  assume a b c d f x x' xx' y y' yy' z z' zz'; rewrite xx'; rewrite yy'; rewrite zz'; reflexivity
end;

opaque symbol feq4 [a b c d e] (f:τ a → τ b →  τ c → τ d → τ e):
  Π [x1 x1':τ a], π(x1 = x1') →
  Π [x2 x2':τ b], π(x2 = x2') →
  Π [x3 x3':τ c], π(x3 = x3') →
  Π [x4 x4':τ d], π(x4 = x4') →
  π(f x1 x2 x3 x4 = f x1' x2' x3' x4') ≔
begin
  assume a b c d e f;
  assume x1 x1' H1;
  assume x2 x2' H2;
  assume x3 x3' H3;
  assume x4 x4' H4;
  rewrite H1;
  rewrite H2;
  rewrite H3;
  rewrite H4;
  reflexivity
end;

opaque symbol feq5 [a b c d e g] (f:τ a → τ b →  τ c  → τ d → τ e → τ g ):
  Π [x1 x1':τ a], π(x1 = x1') →
  Π [x2 x2':τ b], π(x2 = x2') →
  Π [x3 x3':τ c], π(x3 = x3') →
  Π [x4 x4':τ d], π(x4 = x4') →
  Π [x5 x5':τ e], π(x5 = x5') →
  π(f x1 x2 x3 x4 x5 = f x1' x2' x3' x4' x5') ≔
begin
  assume a b c d e g f;
  assume x1 x1' H1;
  assume x2 x2' H2;
  assume x3 x3' H3;
  assume x4 x4' H4;
  assume x5 x5' H5;
  rewrite H1;
  rewrite H2;
  rewrite H3;
  rewrite H4;
  rewrite H5;
  reflexivity
end;

builtin "bot" ≔ ⊥;
builtin "top" ≔ ⊤;
builtin "imp" ≔ ⇒;
builtin "and" ≔ ∧;
builtin "or"  ≔ ∨;
builtin "not" ≔ ¬;
builtin "eqv"  ≔ ⇔;

opaque symbol cong_or [t1 t2 u1 u2: τ o]: π̇ ((t1 = u1) ⸬ □) → π̇ ((t2 = u2) ⸬ □) → π̇ (((t1 ∨ t2) = (u1 ∨ u2)) ⸬ □) ≔
begin
  assume t1 t2 u1 u2 H1 H2;
  have H1': π (t1 = u1) { apply π̇ₗ H1 };
  have H2': π (t2 = u2) { apply π̇ₗ H2 };
  apply ∨ᵢ₁;
  rewrite H1';
  rewrite H2';
   reflexivity
end;

opaque symbol cong_and [t1 t2 u1 u2: τ o]: π̇ ((t1 = u1) ⸬ □) → π̇ ((t2 = u2) ⸬ □) → π̇ (((t1 ∧ t2) = (u1 ∧ u2)) ⸬ □) ≔
begin
  assume t1 t2 u1 u2 H1 H2;
  have H1': π (t1 = u1) { apply π̇ₗ H1 };
  have H2': π (t2 = u2) { apply π̇ₗ H2 };
  apply ∨ᵢ₁;
  rewrite H1';
  rewrite H2';
   reflexivity
end;

opaque symbol cong_imp [t1 t2 u1 u2: τ o]: π̇ ((t1 = u1) ⸬ □) → π̇ ((t2 = u2) ⸬ □) → π̇ (((t1 ⇒ t2) = (u1 ⇒ u2)) ⸬ □) ≔
begin
  assume t1 t2 u1 u2 H1 H2;
  have H1': π (t1 = u1) { apply π̇ₗ H1 };
  have H2': π (t2 = u2) { apply π̇ₗ H2 };
  apply ∨ᵢ₁;
  rewrite H1';
  rewrite H2';
   reflexivity
end;


opaque symbol subst_equiv_clause : Π (x y : 𝕃 o), π (disj x = disj y) → π̇ x → π̇ y ≔
begin
assume x y;
simplify;
assume Heq; assume Hx;
rewrite left Heq;
apply Hx
end;


/**********************************************
* N-ary rules
**********************************************/

symbol literal ≔ nth ⊥;
symbol literals ≔ nths ⊥;

symbol ∈ₙ ≔ ∈ eqn;
notation ∈ₙ infix right 40;

symbol conj : 𝕃 o → τ o;
rule conj ($l1 ⸬ ($c ⸬ $l)) ↪ ($l1 ∧ conj ($c ⸬ $l))
with conj ($l1 ⸬ □) ↪ $l1 
with conj □ ↪ ⊤;

opaque symbol conj_head (c0 : τ o) (c : 𝕃 o) : 
     π (conj (c0 ⸬ c)) → π (c0) ≔
begin
    assume c0;
    induction
        {assume h1;
        refine h1}   
        {assume x0 c1 h1 h2;
        refine ∧ₑ₁ h2}
end; 

symbol indexes_shift (l: 𝕃 nat) (n : τ nat):
    π (istrue ((n +1) ∈ₙ (map (+1) l)) ⇒ istrue (n ∈ₙ l))≔
begin
  induction
      {assume n x; refine x}
      {assume n0;
      induction
          {assume h0 n h1; refine h1}
          {assume n1 l h0 h1 n2 h2;
          refine orₑ [eqn n2 n0] [eqn n2 n1 Stdlib.Bool.or ∈ eqn (n2 +1) (map (+1) l)] (eqn n2 n0 Stdlib.Bool.or (eqn n2 n1 Stdlib.Bool.or ∈ eqn n2 l)) h2 _ _
              {assume h3;
              refine orᵢ₁ (eqn n2 n1 Stdlib.Bool.or ∈ eqn n2 l) h3}
              {assume h3;
              refine orᵢ₂ (eqn n2 n0) (h1 n2 h3)}}}
end;

symbol indexes_decrement (id : τ nat) (l0: τ o) (l: 𝕃 o): 
     π ((id +1) ∈ₙ (indexes (l0 ⸬ l))) → π (id ∈ₙ (indexes l))≔
begin
    assume id l0 l;
    assume h0; 
    have H1 : π ((istrue (∈ eqn (id +1) (iota 1 (size l)))) ⇒ (istrue (∈ eqn id (iota 0 (size l)))))
        {have H2: π (iota 1 (size l) = map (+1) (iota 0 (size l)))
            {refine (eq_sym (mapS_iota (size l) 0))};
        rewrite H2;
        refine indexes_shift (iota 0 (size l)) id};
    refine H1 h0
end;


opaque symbol literal_ext (l: 𝕃 o) (l0 : τ o) (n: τ nat) : 
    π (literal l n) → π (literal (l0 ⸬ l) (n +1)) ≔
begin
    simplify;
    assume l l0 n h1;
    refine h1
end;

opaque symbol conj_tail (c0 : τ o) (c : 𝕃 o) : 
     π (conj (c0 ⸬ c)) → π (conj c) ≔
begin
    assume c0;
    induction
        {assume h1;
        refine ⊤ᵢ}   
        {assume x0 c1 h1 h2; 
        refine ∧ₑ₂ h2}
end; 

opaque symbol select (k : τ nat) (cnf: 𝕃 o) : 
    π (k ∈ₙ (indexes cnf)) → π (conj cnf) → π (literal cnf k) ≔
begin
    induction 
        {induction
            {assume h0 h1; refine h0}
            {assume x cnf h0 h1 h2; 
            refine conj_head x cnf h2}}
        {assume k h0;
        induction
            {assume b; refine ⊥ₑ b}
            {assume x xs ih h2 h3;
            have ConjImpCl : π (conj xs ⇒ literal xs k)
                {refine h0 xs (indexes_decrement k x xs h2)};
            simplify;
            refine literal_ext xs x k (ConjImpCl (conj_tail x xs h3))}}
end;

// Rule and:
// i. ▷ (𝜑1 ∧ ⋯ ∧ 𝜑𝑛)
// j. ▷ 𝜑𝑘
symbol negate: 𝕃 o → 𝕃 o;
rule negate □ ↪ □
with negate ($x ⸬ $xs) ↪ ¬ $x ⸬ negate $xs;

opaque symbol disj_head (l0 : τ o) (l : 𝕃 o) : 
    π (l0) → π (disj (l0 ⸬ l)) ≔
begin
    assume l0;
    induction
        {assume h1; simplify; rewrite or_identity_r;
        refine h1}   
        {assume x0 l1 h1 h2; 
        refine ∨ᵢ₁ h2}
end; 

opaque symbol disj_tail (l0 : τ o) (l : 𝕃 o) : 
    π (disj l) → π (disj (l0 ⸬ l)) ≔
begin
    assume l0;
    induction
        {assume h1;
        refine ⊥ₑ h1}
        {assume x1 l1 h1 h2;
        refine ∨ᵢ₂ h2}
end;

opaque symbol disj_correct (l0 : τ o) (l : 𝕃 o) : 
    π (disj (l0 ⸬ l)) → π (l0 ∨ disj l) ≔
begin
    assume l0;
    induction
        {
          assume h1;
          refine h1
        }
        {assume x1 l1 h1 h2;
        refine h2}
end;

opaque symbol disj_complete (l0 : τ o) (l : 𝕃 o) : 
    π (l0 ∨ disj l) → π (disj (l0 ⸬ l))  ≔
begin
    assume l0;
    induction
        {
          refine (λ x, x)
        }
        {assume x1 l1 h1 h2;
        refine h2}
end;

opaque symbol disj_eq (l0 : τ o) (l : 𝕃 o) :  π ((l0 ∨ disj l) = disj (l0 ⸬ l)) ≔
begin
  assume x l;
  apply prop_ext;
  apply ∧ᵢ 
  { refine disj_complete x l }
  { refine disj_correct x l }
end;

opaque symbol conj_correct (c0 : τ o) (c : 𝕃 o) : 
    π (conj (c0 ⸬ c)) → π (c0 ∧ conj c) ≔
begin
    assume c0;
    induction
        {assume h1;
        refine ∧ᵢ h1 ⊤ᵢ}
        {assume x1 c1 h1 h2;
        refine h2}
end;

opaque symbol conj_complete (c0 : τ o) (c : 𝕃 o) : 
     π (c0 ∧ conj c) → π (conj (c0 ⸬ c)) ≔
begin
    assume c0;
    induction
        {assume h1; simplify;
        refine ∧ₑ₁ h1}
        {assume x1 c1 h1 h2;
        refine h2}
end;

opaque symbol conj_eq (l0 : τ o) (l : 𝕃 o) :  π ((l0 ∧ conj l) = conj (l0 ⸬ l)) ≔
begin
  assume x l;
  apply prop_ext;
  apply ∧ᵢ 
  { refine conj_complete x l }
  { refine conj_correct x l }
end;
 
// and_neg:  (𝜑1 ∧ ⋯ ∧ 𝜑𝑛), ¬𝜑1, … , ¬𝜑𝑛
symbol sym_clause x y : π̇ (x ⸬ y ⸬ □) → π̇ (y ⸬ x ⸬ □) ≔
begin
simplify;
assume x y h;
rewrite left  ∨_assoc;
rewrite ∨_com y x;
rewrite ∨_assoc;
refine h
end;

symbol eraseIdx [a] : 𝕃 a → ℕ → 𝕃 a;
rule eraseIdx □ _ ↪ □
with eraseIdx (_ ⸬ $xs) 0 ↪ $xs
with eraseIdx ($x ⸬ $xs) ($n +1) ↪ $x ⸬ (eraseIdx $xs $n);

assert ⊢ (eraseIdx (0 ⸬ 1 ⸬ 2 ⸬ 3 ⸬ □) 2) ≡ (0 ⸬ 1 ⸬ 3 ⸬ □);
assert ⊢ (eraseIdx (0 ⸬ 1 ⸬ 2 ⸬ 3 ⸬ □) 5) ≡ (0 ⸬ 1 ⸬ 2 ⸬ 3 ⸬ □);
assert ⊢ (eraseIdx  □ 2) ≡ □;

opaque symbol case_l [a] x (l: 𝕃 a) n : π ((n +1) ≤ (size (x ⸬ l))) → π (n ≤ (size l)) ≔
begin
  assume a x l n H;
  refine H
end;

symbol orN_eraseIdx qs j (hj: π (j < size qs)) : π ((disj (eraseIdx qs j) ∨ (nth ⊥ qs j)) = (disj qs)) ≔
begin
  induction
  {
    assume j;
    simplify;
    assume contra;
    refine ⊥ₑ contra
  }
  {
    assume t l ih;
    induction
    {
      simplify;
      assume h;
      rewrite ∨_com;
      reflexivity
    }
   {
      assume j ih2 h; print <;
      simplify;
      rewrite left ih j (case_l t l (j +1) h);
      remove ih2;
      rewrite left ∨_assoc;
      reflexivity
    }
  }
end;

print ind_ℕ;

symbol rec_ℕ : Π p0: (ℕ → Prop), π (p0 0) → (Π x0: ℕ, π (p0 (x0 +1))) → Π x: ℕ, π (p0 x);

symbol sublist [a] (xs : 𝕃 a) (i j : ℕ) ≔ drop i (take j xs);

symbol orN_subList (qs ps : 𝕃 o)  (i j : ℕ) (hps : π (disj ps)) (hpq : π (ps = sublist qs i j)) : π (disj qs) ≔
begin
  induction // qs
  {
    assume x i j h1 heq;
    change π (disj (sublist □ i j));
    rewrite left heq;
    apply h1    
  }
  {
    assume t l ih;
    assume  ps i;
    refine rec_ℕ (λ j, disj ps ⇒ ((ps = sublist (t ⸬ l) i j) ⇒ disj (t ⸬ l))) _ _
    {
      simplify;
      assume hp hps;
      apply ∨ᵢ₂;
      refine ih ps i 0 hp hps;
    }
    {
      assume j;
      generalize i;
      refine rec_ℕ (λ i, `∀ j, disj ps ⇒ ((ps = sublist (t ⸬ l) i (j +1)) ⇒ disj (t ⸬ l))) _ _
      {
        simplify;
        assume j hps heq;
        type ih ps 0 j hps;
        compute sublist l 0 j;
        have g: π (t ∨ disj (take j l)) {
          change π (disj (t ⸬ take j l));
          rewrite left heq;
          apply hps
        };
        apply ∨ₑ g
        { assume ht; apply ∨ᵢ₁; refine ht }
        { assume g2; apply ∨ᵢ₂; apply ih (drop 0 (take j l)) 0 j g2 (eq_refl _) }
      }
      {
        simplify;
        assume i j hp hps;
        apply ∨ᵢ₂;
        apply ih ps i j hp hps;
      }
    }
  }
end;

symbol orN_append_right (ps qs : 𝕃 o) (hqs : π (disj qs)) : π (disj (ps Stdlib.List.++ qs)) ≔
begin
  assume ps qs hqs;
  apply orN_subList (ps Stdlib.List.++ qs) qs  (size ps) (size ps + size qs) hqs;
  simplify;
  rewrite left size_cat;
  rewrite take_size;
  rewrite drop_size_cat (size ps) ps qs (eq_refl _);
  reflexivity
end;

symbol orN_append_left (ps qs : 𝕃 o) (hqs : π (disj ps)) : π (disj (ps Stdlib.List.++ qs)) ≔
begin
  assume ps qs hps;
  apply orN_subList (ps Stdlib.List.++ qs) ps  0 (size ps) hps;
  simplify;
  rewrite take_size_cat (size ps) ps qs (eq_refl _);
  reflexivity
end;

// Used when carcara put the flag at `false`
symbol disj_resolutionN1 (ps qs:  𝕃 o) (i j: ℕ)
  (hps: π (disj ps))
  (hqs: π (disj qs))
  (hi: π (i < size ps))
  (hj: π (j < size qs))
  (hij: π ((nth ⊥ ps i) = ¬ (nth ⊥ qs j))) : π (disj ((eraseIdx ps i) Stdlib.List.++ (eraseIdx qs j))) ≔
begin
assume ps qs i j;
have h: π ((nth ⊥ ps i) ∨ ¬ (nth ⊥ ps i)) { refine em (nth ⊥ ps i) };
assume hps hqs hi hj hij;
have h1: π ((disj (eraseIdx ps i) ∨ nth ⊥ ps i) = disj ps) { refine  orN_eraseIdx ps i hi };
have h2: π ((disj (eraseIdx qs j) ∨ nth ⊥ qs j) = disj qs) { refine orN_eraseIdx qs j hj };
apply ∨ₑ h
{
  assume hp;
  have hij': π (nth ⊥ ps i ⇔ ¬ (nth ⊥ qs j)) { rewrite hij; apply ⇔_refl };
  have h3: π (¬ (nth ⊥ qs j)) { refine ∧ₑ₁ hij' hp };
  have hps': π ((disj (eraseIdx ps i) ∨ ¬ (nth ⊥ qs j))) { rewrite left hij; apply ∨ᵢ₂; refine hp };
  remove hps;
  remove h1;
  have hqs': π ((disj (eraseIdx qs j) ∨ nth ⊥ qs j)) { rewrite h2; apply hqs };
  remove h2;
  remove hqs;
  have g: π ((⊥ = nth ⊥ qs j)) { rewrite ⊥= (nth ⊥ qs j); refine h3 };
  have hqs'': π (disj (eraseIdx qs j)) { rewrite left or_identity_r; rewrite g; refine hqs' };
  apply orN_append_right (eraseIdx ps i) (eraseIdx qs j) hqs'';
}
{
  assume hp;
   have g: π ((⊥ = nth ⊥ ps i)) { rewrite ⊥= (nth ⊥ ps i); refine hp };
   have hps': π ((disj (eraseIdx ps i))) { rewrite left or_identity_r; rewrite g;  rewrite h1; apply hps };
   have hqs': π ((disj (eraseIdx qs j) ∨ nth ⊥ qs j)) { rewrite h2; apply hqs };
  apply orN_append_left (eraseIdx ps i) (eraseIdx qs j) hps';
}
end;

// Used when carcara put the flag at `true`
symbol disj_resolutionN2 (ps qs:  𝕃 o) (i j: ℕ)
  (hps: π (disj ps))
  (hqs: π (disj qs))
  (hi: π (i < size ps))
  (hj: π (j < size qs))
  (hij: π (¬ (nth ⊥ ps i) = (nth ⊥ qs j))) : π (disj ((eraseIdx ps i) Stdlib.List.++ (eraseIdx qs j))) ≔
begin
admit
end;




/* ------------------------------------------------------------------------
   Tactics (was alethe.Tactic)
   ------------------------------------------------------------------------ */

unif_rule @η $l $a ≡ Π x:Prop, π $c.[x] ↪
  [$l ≡ prop; $a ≡ @∀ o (λ x:Prop, $c.[x])];
unif_rule @η $l $a ≡ Π x:Prop, Π y:Prop, π $c.[x;y] ↪
  [$l ≡ prop; $a ≡ @∀ o (λ x:Prop, @∀ o (λ y:Prop, $c.[x;y]))];
unif_rule @η $l $a ≡ Π x:Prop, Π y:Prop, Π z:Prop, π $c.[x;y;z] ↪
  [$l ≡ prop; $a ≡ @∀ o (λ x:Prop, @∀ o (λ y:Prop, @∀ o (λ z:Prop, $c.[x;y;z])))];
unif_rule @η $l $a ≡ Π x:τ $s.[], Π y:τ $s.[], π $c.[x;y] ↪
  [$l ≡ prop; $a ≡ @∀ $s.[] (λ x:τ $s.[], @∀ $s.[] (λ y:τ $s.[], $c.[x;y]))];
unif_rule @η $l $a ≡ Π b:Prop, Π x:τ $s.[], Π y:τ $s.[], π $c.[b;x;y] ↪
  [$l ≡ prop; $a ≡ @∀ o (λ b:Prop, @∀ $s.[] (λ x:τ $s.[], @∀ $s.[] (λ y:τ $s.[], $c.[b;x;y])))];
unif_rule @η $l $a ≡ Π b:Prop, Π x:τ $s.[], Π y:τ $s.[], Π z:τ $s.[], π $c.[b;x;y;z] ↪
  [$l ≡ prop; $a ≡ @∀ o (λ b:Prop, @∀ $s.[] (λ x:τ $s.[], @∀ $s.[] (λ y:τ $s.[], @∀ $s.[] (λ z:τ $s.[], $c.[b;x;y;z]))))];

// A module that contains string literals must carry the "String" builtin itself:
// the .lpo loader (handle/compile.ml) looks it up in this module's builtin table.
builtin "String" ≔ Stdlib.String.String;

// Set-level codes so that lists of strings / tactics can be formed.

constant symbol string : Set;
rule τ string ↪ String;

symbol tactic : Set;
rule τ tactic ↪ Tactic;

// Tactic composition was historically spelled `and`.
symbol and : Tactic → Tactic → Tactic ≔ &;
notation and infix right 15;

notation #orelse infix left 10;
notation #repeat prefix 2;

// `#rewrite_gen "left" "pattern" h` and the short `#rewrite h` form.
symbol #rewrite_gen (dir pat : String) [l] [a:U l] (h : η a) : Tactic ≔
  Stdlib.Tactic.#rewrite dir pat h;

symbol #rewrite [l] [a:U l] (h : η a) : Tactic ≔ Stdlib.Tactic.#rewrite "" "" h;

/*****************************************************************************/

symbol #do : ℕ → Tactic → Tactic;

rule #do 0 _ ↪ nothing
with #do ($n +1)  $t ↪ $t and (#do $n $t);

// Used to remove trailing `⊥` due to usage of disj or disj
// in order to compare left and right term in simplification rule.
symbol #repeat_or_id_r : Tactic ≔ #repeat (#rewrite or_identity_r);

/******************************************************************************
*  Definition of Alethe meta tactic
******************************************************************************/

symbol applyAny : 𝕃 tactic → Tactic;
rule applyAny ($t0 ⸬ $tl) ↪ $t0 #orelse (applyAny $tl)
with applyAny Stdlib.List.□ ↪ #fail;


/* ------------------------------------------------------------------------
   Clause reification, sorting and contraction (was alethe.Clause)
   ------------------------------------------------------------------------ */

protected symbol compN : ℕ → ℕ → Comp;

rule compN _0 _0 ↪ Eq
with compN _0 (_ +1) ↪ Lt
with compN (_ +1) _0 ↪ Gt
with compN ($x +1) ($y +1) ↪ compN $x $y;

protected opaque symbol compN_correct x y : π (compN x y = Eq ⇒ x = y) ≔
begin
induction
{ induction
  {assume h; reflexivity}
  {assume y hy h; apply ⊥ₑ; apply Lt≠Eq h}
}
{ assume x hx; induction
  {assume h; apply ⊥ₑ; apply Gt≠Eq h}
  {assume y hy h; apply feq (+1); apply hx y h }
}
end;

inductive ClauseAlg : TYPE ≔
| p : ℕ → ClauseAlg;

symbol cl : Set;
rule τ cl ↪ ClauseAlg;


symbol compCl : ClauseAlg → ClauseAlg → Comp;
rule compCl (p $i) (p $j) ↪ compN $i $j
;

symbol split [a: Set] (l : τ (list a)): τ(list a × list a);
rule split □ ↪ (□ ‚ □)
with split ($x ⸬ □) ↪ (($x ⸬ □) ‚ □)
with split ($x ⸬ $y ⸬ $l) ↪
    let res ≔  (split $l) in
        ($x ⸬ (res ₁)) ‚ ($y ⸬ (res ₂));

symbol list_ind2_principle [A : Set]  :
  Π (P : τ (list A) → Prop),
    π (P □) →
    (Π (a: τ A), π (P (a ⸬ □))) →
    (Π (a b : τ A) (l : τ (list A)), π (P l) →  π (P (a ⸬ b ⸬ l))) →
    Π (l : τ (list A)), π (P l);


symbol den: 𝕃 o → 𝕃 cl → Prop;
rule den $σ □ ↪ ⊥
with den $σ ((p $i) ⸬ $xs) ↪ (nth ⊥ $σ $i) ∨ (den $σ $xs)
;



constant symbol R : TYPE;
constant symbol Index : ℕ → R;
constant symbol New : ℕ → R;

symbol case [a] : R → (ℕ → τ a) → (ℕ → τ a) → τ a;

rule case (Index $i) $f _ ↪ $f $i
with case (New $i) _ $g ↪ $g $i;

/* index of a value in a list: returns New if the value is not
definitionally equivalent to some element of the list */

sequential symbol index: ℕ → Π [a], τ a → τ(list a) → R;

rule index $k _ □ ↪ New $k
with index $k $x ($x ⸬ _) ↪ Index $k
with index $k $x ($y ⸬ $l) ↪ index ($k +1) $x $l;

//compute case (New Stdlib.Nat._0) (λ i, (p i) ‚ (□)) (λ i, (p i) ‚ (⊤ ⸬ □));

symbol rfy_cl: 𝕃 o → 𝕃 o → τ (list cl × list o);
rule rfy_cl $l □ ↪ (□ ‚ $l)
with rfy_cl $l ($x ⸬ $xs) ↪ 
  let X ≔  case (index 0 $x $l) (λ i, (p i) ‚ $l) (λ i, (p i) ‚ ($l Stdlib.List.++ ($x ⸬ □))) in
  let x ≔ X ₁ in
  let l' ≔ X ₂ in
  let xs ≔ rfy_cl l' $xs in
    ((x ⸬ (xs ₁)) ‚ (xs ₂));

symbol reify_cl ≔ rfy_cl □;

compute reify_cl (a ⸬ b ⸬ □);

compute  den ((reify_cl (a ⸬ b ⸬ □)) ₂) ((reify_cl (a ⸬ b ⸬ □)) ₁);

assert a b ⊢ reify_cl (a ⸬ b ⸬ □) ≡ (((p 0) ⸬ (p 1) ⸬ □) ‚ (a ⸬ b ⸬ □));

assert a b ⊢ den ((reify_cl (a ⸬ b ⸬ □)) ₂) ((reify_cl (a ⸬ b ⸬ □)) ₁) ≡  disj (a ⸬ b ⸬ □);

opaque symbol ++_eq_∨ l x y : π ((den l (x Stdlib.List.++ y)) = (den l x ∨ den l y)) ≔
begin
    assume l;
    induction
    {
        assume y;
        simplify;
        rewrite or_identity_l;
        reflexivity
    }
    {
        induction;
        assume i xs ih;
        assume y;
        simplify;
        rewrite ih;
        rewrite left ∨_assoc;
        reflexivity
    }
end;

// symbol flat: τ(list cl) → τ cl;

// rule flat □ ↪ Cst 0
// with flat ($x ⸬ $l) ↪ Add $x (sum $l);

opaque symbol split_correct l gs : π (den l ((split gs ₁) Stdlib.List.++ (split gs ₂)) = den l gs) ≔
begin
assume l;
refine list_ind2_principle (λ u, den l ((split u ₁) Stdlib.List.++ (split u ₂)) = den l u) _ _ _
{ reflexivity }
{ reflexivity }
{
    induction;
    assume i;
    induction;
    assume j;
    assume tl ih;
    simplify;
    rewrite left ih;
    rewrite ++_eq_∨;
    rewrite ++_eq_∨;
    simplify;
    rewrite left .[in x in (_ ∨ x ) = _] ∨_assoc;
    rewrite .[in x in (_ ∨ (x ∨ _) ) = _] ∨_com;
    rewrite .[in x in (_ ∨ x ) = _] ∨_assoc;
    reflexivity
}
end;

symbol merge  (l1 l2 : τ (list cl)): τ (list cl);
rule merge □ □ ↪ □
with merge □ $l2 ↪ $l2
with merge $l1 □ ↪ $l1
with merge (p $i ⸬ $l1') (p $j ⸬ $l2') ↪
    case_Comp (compN $i $j)
        (p $i ⸬ p $j ⸬ merge $l1' $l2')
        ((p $i) ⸬ merge $l1' (p $j ⸬ $l2'))
        (p $j ⸬ merge (p $i ⸬ $l1') $l2')
;


opaque symbol merge_correct l g1 g2 :  π (den l (merge  g1 g2) = (den l g1  ∨ den l g2)) ≔
begin
  assume l;
  induction
  {
        simplify; assume g2;
        rewrite or_identity_l; reflexivity
  }
  {
        induction; assume i xs ih;
        induction
        {
            simplify;
            rewrite or_identity_r; reflexivity
        }
        {
            induction;
            assume j ys ih2;
            simplify;
            refine ind_Comp (λ u, (compN i j) = u ⇒  (den l (case_Comp u (p i ⸬ (p j ⸬ merge xs ys)) (p i ⸬ merge xs (p j ⸬ ys)) (p j ⸬ merge (p i ⸬ xs) ys)) = ((nth ⊥ l i ∨ den l xs) ∨ (nth ⊥ l j ∨ den l ys)))) _ _ _ (compN i j) _
            {
                simplify;
                assume heq;
                rewrite ih;
                rewrite .[x in _ = x] ∨_assoc;
                rewrite left  .[x in _ = ( _ ∨ x)] ∨_assoc;
                rewrite ∨_com (den l xs) (nth ⊥ l j);
                rewrite  .[x in _ = ( _ ∨ x)] ∨_assoc;
                reflexivity
            }
            {
                simplify; assume hlt;
                rewrite ih;
                simplify;
                rewrite left ∨_assoc;
                reflexivity
            }
            {
                simplify;
                assume hgt;
                rewrite ih2;
                simplify;
                rewrite .[x in (_ ∨ x) = _] ∨_com;
                rewrite left ∨_assoc;
                rewrite ∨_com;
                reflexivity
            }
            {reflexivity}
        }
  }
end;


symbol mergesort:  τ (list cl) →  τ (list cl);
rule mergesort □ ↪ □
with mergesort ($x ⸬ □) ↪ ($x ⸬ □)
with mergesort ($x ⸬ $y ⸬ $l) ↪
    let s ≔ split ($x ⸬ $y ⸬ $l) in
    let l1 ≔ s ₁ in
    let l2 ≔ s ₂ in
        merge (mergesort l1) (mergesort l2);



opaque symbol rec_𝕃 : Π [a: Set], Π l: 𝕃 a, Π p: (𝕃 a → Prop), π (p □) → (Π x0: τ a, Π l': 𝕃 a, π (p (x0 ⸬ l'))) → π (p l) ≔
begin
  assume a l P H1 H2;
  refine @ind_𝕃 a P H1 (λ x l' ih, H2 x l') l
end;

opaque symbol case_l_size [a] x (l: 𝕃 a) n : π ((size (x ⸬ l)) ≤ (n +1)) → π (size l ≤ n) ≔
begin
  assume a x l n;
  refine λ x, x;
end;

opaque symbol size_split [a] (l: 𝕃 a) : π (size ((split l) ₁) ≤ size l) ≔
begin
  assume a;
  refine list_ind2_principle (λ u, istrue (size (split u ₁) ≤ size u)) _ _ _
  {apply ⊤ᵢ}
  {assume y; apply ⊤ᵢ}
  {
    simplify;
    assume x y l ih;
    apply @leq_trans (size (split l ₁)) (size l) (size l +1) ih _;
    refine leqnSn (size l)
  }
end;

opaque symbol size_split2 [a] (l: 𝕃 a) : π (size ((split l) ₂) ≤ size l) ≔
begin
  assume a;
  refine list_ind2_principle (λ u, istrue (size (split u ₂) ≤ size u)) _ _ _
  {apply ⊤ᵢ}
  {assume y; apply ⊤ᵢ}
  {
    simplify;
    assume x y l ih;
    apply @leq_trans (size (split l ₂)) (size l) (size l +1) ih _;
    refine leqnSn (size l)
  }
end;


opaque symbol mergesort_correct_aux n l g : π (size g ≤ n) →  π (den l (mergesort g) = den l g) ≔
begin
induction
{
    assume l g h;
    rewrite size0nil g (≤0 (size g) h);
    reflexivity
}
{
    assume n ihn l g;
    refine rec_𝕃 g (λ g, (istrue (size g ≤ (n +1))) ⇒ (den l (mergesort g) = den l g)) _ _
    { simplify; assume h; reflexivity }
    {
        induction; assume i gs;
        refine rec_𝕃 gs (λ gs, istrue (size (p i ⸬ gs) ≤ (n +1)) ⇒ (den l (mergesort (p i ⸬ gs)) = den l (p i ⸬ gs))) _ _
        {
            simplify;
            assume h;
            reflexivity
        }
        {
            induction;
            assume j xs inv;
            simplify;
            rewrite merge_correct;
            have h1:  π ((size (p i ⸬ (split xs ₁))) ≤ n) {
                apply @leq_trans
                (size (split xs ₁) +1)
                (size xs +1)
                n
                _
                inv;
                apply size_split xs;
            };
            have h2:  π ((size (p j ⸬ (split xs ₂))) ≤ n) {
                apply @leq_trans
                (size (split xs ₂) +1)
                (size xs +1)
                n
                _
                inv;
                apply size_split2 xs;
            };
            rewrite ihn l (p i ⸬ (split xs ₁)) h1;
            rewrite ihn l (p j ⸬ (split xs ₂)) h2;
            simplify;
            rewrite ∨_assoc;
            rewrite left .[x in (_ ∨ x) = _] ∨_assoc;
            rewrite ∨_com (den l (split xs ₁)) (nth ⊥ l j);
            rewrite ∨_assoc;
            rewrite left ++_eq_∨ l (split xs ₁) (split xs ₂);
            rewrite split_correct;
            reflexivity
        }
    }
}
end;

symbol mergesort_correct l g ≔ mergesort_correct_aux (size g) l g (≤_refl (size g));

symbol remove_iden: τ (list cl) → τ (list cl);
rule remove_iden □ ↪ □
with remove_iden ((p $i) ⸬ □) ↪ (p $i) ⸬ □
with remove_iden ((p $i) ⸬ (p $j) ⸬ $tl) ↪ case_Comp (compN $i $j)
                                            (remove_iden ((p $j) ⸬ $tl))
                                            ((p $i) ⸬ (remove_iden ((p $j) ⸬ $tl)))
                                            ((p $i) ⸬ (remove_iden ((p $j) ⸬ $tl)));


// Rule contraction:
// 𝑖. ⊳ 𝑙1, ... , 𝑙n    (...)
// 𝑗. ⊳  𝑙𝑘1, ... , 𝑙kn (contraction i)
symbol contraction g ≔ remove_iden (mergesort g);

opaque symbol remove_iden_correct l g : π (den l (remove_iden g) = den l g) ≔
begin
  assume l;
  induction
  {simplify;reflexivity}
  {
    induction; assume i;
    induction
    {
      assume h; reflexivity
    }
    {
      induction; assume j gs ih1 ih2;
      simplify;
      refine ind_Comp (λ u, (compN i j) = u ⇒  den l (case_Comp u (remove_iden (p j ⸬ gs)) (p i ⸬ remove_iden (p j ⸬ gs)) (p i ⸬ remove_iden (p j ⸬ gs))) = (nth ⊥ l i ∨ (nth ⊥ l j ∨ den l gs))) _ _ _ (compN i j) _
      {
        simplify;
        assume heq;
        rewrite compN_correct i j heq;
        rewrite left ∨_assoc;
        rewrite or_idempotent (nth ⊥ l j);
        rewrite ih2;
        reflexivity
      }
      {
        simplify;
        assume hlt;
        rewrite ih2;
        reflexivity
      }
      {
        simplify;
        assume hlt;
        rewrite ih2;
        reflexivity
      }
      {reflexivity}
    }
  }
end;

opaque symbol contraction_correct l g : π (den l (contraction g) = den l g) ≔
begin
  assume l g;
  simplify;
  rewrite remove_iden_correct;
  rewrite mergesort_correct;
  reflexivity
end;

opaque symbol contraction_correct_r l g : π (den l g = den l (contraction g)) ≔
begin
  assume l g;
  symmetry;
  refine contraction_correct l g
end;

private symbol example a b : π̇ (a ⸬ b ⸬ b ⸬ □) → π̇ (a ⸬ b ⸬ □) ≔
begin
  assume a b i;
  set X ≔ (a ⸬ (b ⸬ (b ⸬ □)));
  set Y ≔ (a ⸬ b ⸬ □);
  have g : π (disj X = disj Y) {
    set r ≔ reify_cl X;
    change π (den (r ₂) (r ₁) = disj Y);
    rewrite left contraction_correct;
    reflexivity
  };
  refine subst_equiv_clause X Y  g i
end;

