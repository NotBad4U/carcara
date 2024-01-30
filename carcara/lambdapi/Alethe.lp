require open Stdlib.Prop;
require open Stdlib.FOL;
require open Stdlib.Set;
require open Stdlib.Nat;
require open Stdlib.Eq;
require open Stdlib.Bool;
require open Stdlib.List;

symbol o: Set;
rule τ o ↪ Prop;

// # Clause
// Clauses are encoded with list à la Church Encoding.
// This encoding is necessary because Inductive type in Lambdapi
// could not live in Prop.
constant symbol Clause : TYPE;

// Nil
symbol ▩ : Clause; 
// Cons
injective symbol ⟇: Prop → Clause → Clause;
notation ⟇ infix right 2;
// Append of two clause list
sequential symbol ++ : Clause → Clause → Clause; notation ++ infix right 3;

rule ▩ ++ $m ↪ $m
with ($x ⟇ $l) ++ $m ↪ $x ⟇ ($l ++ $m);

constant symbol Clause_ind:  Π P: (Clause → Prop), Π l,
  π (P ▩) →
  (Π x: Prop, Π l: Clause, π (P l) → π (P (x ⟇ l))) →
  π (P l);

// some sanity checks
assert x y z ⊢ x ++ y ++ z ≡ x ++ (y ++ z);
assert x l m ⊢ x ⟇ l ++ m ≡ x ⟇ (l ++ m);

injective symbol ¬ᶜ : Prop → Prop; notation ¬ᶜ prefix 8;

// FIXME: 
constant symbol ¬ᶜₑ [p q] : π (¬ᶜ p) → π p → π q;

injective symbol ∨ᶜ : Prop → Prop → Prop; notation ∨ᶜ infix right 12;

// Introduction and elimination for classical or
constant symbol ∨ᶜᵢ₁ [p q] : π p → π (p ∨ᶜ q);
constant symbol ∨ᶜᵢ₂ [p q] : π q → π (p ∨ᶜ q);
symbol ∨ᶜₑ [p q r] : π (p ∨ᶜ q) → (π p → π r) → (π q → π r) → π r;

symbol ∨ᶜ_com [x y] : π (x ∨ᶜ y) → π (y ∨ᶜ x) ≔
begin
  assume x y hxy;
  apply ∨ᶜₑ hxy
  { assume hx; apply ∨ᶜᵢ₂; apply hx }
  { assume hy; apply ∨ᶜᵢ₁; apply hy }
end;


sequential symbol ∨ᶜ_to_⟇_rw: Prop → Clause;
rule ∨ᶜ_to_⟇_rw ($x ∨ᶜ $y) ↪ $x ⟇ (∨ᶜ_to_⟇_rw $y)
with ∨ᶜ_to_⟇_rw ⊥ ↪  ▩;

sequential symbol ⟇_to_∨ᶜ_rw: Clause → Prop;
rule ⟇_to_∨ᶜ_rw ($x ⟇ $y) ↪ $x ∨ᶜ (⟇_to_∨ᶜ_rw $y)
with ⟇_to_∨ᶜ_rw ▩ ↪ ⊥;

assert a b ⊢ ⟇_to_∨ᶜ_rw (a ⟇ b ⟇ ▩) ≡ a ∨ᶜ b ∨ᶜ ⊥;
assert a b c ⊢ ∨ᶜ_to_⟇_rw (a ∨ᶜ b ∨ᶜ ⊥ ∨ᶜ c ∨ᶜ ⊥) ≡ (a ⟇ b ⟇ ⊥ ⟇ c ⟇ ▩);

injective symbol π̇ c: TYPE ≔ π (⟇_to_∨ᶜ_rw c);

opaque symbol π̇ₗ [a] : π̇ (a ⟇ ▩)  → π a ≔
begin
  assume a Hcl_a;
  apply @∨ᶜₑ a ⊥ a
  { apply Hcl_a }
  { assume Ha; apply Ha }
  { assume False; apply ⊥ₑ False };
end;

// opaque injective symbol πᶜ p : TYPE ≔ π (¬ (¬ p));

// Introduction rule for Clause
// construct `p ⟇ q` from a clause with only `p`
opaque symbol ⟇ᵢ₁ [p q] : π̇ (p ⟇ ▩) → π̇ (p ⟇ q) ≔
begin
  assume p q Hp;
  apply ∨ᶜₑ Hp
  { assume Hpi_p; apply ∨ᶜᵢ₁;  apply Hpi_p }
  { assume Hbot; apply ⊥ₑ; apply Hbot }
end;

// construct `p ⟇ q` from a proof of `p`
opaque symbol ⟇ᵢ₁' [p q] : π p → π̇ (p ⟇ q) ≔
begin 
  assume p q Hp; apply ∨ᶜᵢ₁; apply Hp
end;

opaque symbol ⟇ᵢ₂ [p q] : π̇ q → π̇ (p ⟇ q) ≔
begin
  assume p q Hq; apply ∨ᶜᵢ₂; apply Hq
end;

// Elimination rule for clause
opaque symbol ⟇ₑ [p q r] : π̇ (p ⟇ q) → (π̇ (p ⟇ ▩) → π̇ r) → (π̇ q → π̇ r) → π̇ r ≔
begin
  assume p q r Hpq Hpr Hqr;
  apply ∨ᶜₑ Hpq
  { assume Hp; apply Hpr (∨ᶜᵢ₁ Hp) }
  { assume Hq; apply Hqr Hq }
end;

opaque  symbol ∨ᶜ_assoc [x y z] : π ((x ∨ᶜ (y ∨ᶜ z)) ⇔ ((x ∨ᶜ y) ∨ᶜ z)) ≔
begin
  assume x y z;
  simplify;
  apply ∧ᵢ
  {
    assume Hxyz;
    apply ∨ᶜₑ Hxyz
    { assume Hx;  apply ∨ᶜᵢ₁; apply ∨ᶜᵢ₁; apply Hx }
    {
      assume Hyz; apply ∨ᶜₑ Hyz
      { assume Hy;  apply ∨ᶜᵢ₁;  apply ∨ᶜᵢ₂; apply Hy }
      { assume Hz;  apply ∨ᶜᵢ₂; apply Hz }
    }
  }
  {
    assume Hxyz;
    apply ∨ᶜₑ Hxyz
    {
      assume Hxy; apply ∨ᶜₑ Hxy
      { assume Hx; apply ∨ᶜᵢ₁; apply Hx }
      { assume Hy; apply ∨ᶜᵢ₂; apply ∨ᶜᵢ₁; apply Hy }
    }
    { assume Hz; apply ∨ᶜᵢ₂; apply ∨ᶜᵢ₂; apply Hz }
  }
end;

opaque symbol ++_to_∨ᶜ a b : π ((⟇_to_∨ᶜ_rw (a ++ b)) ⇔ ((⟇_to_∨ᶜ_rw a) ∨ᶜ (⟇_to_∨ᶜ_rw b))) ≔
begin
  assume a b;
  apply Clause_ind (λ u, (⟇_to_∨ᶜ_rw (u ++ b)) ⇔ ((⟇_to_∨ᶜ_rw u) ∨ᶜ (⟇_to_∨ᶜ_rw b))) a
    {
      simplify;
      apply ∧ᵢ
        { assume H; apply ∨ᶜᵢ₂; apply H }
        {
          assume H;
          apply ∨ᶜₑ H { assume H⊥; apply ⊥ₑ; apply H⊥ } { assume H1;  apply H1}
        }
    }
    {
      simplify;
      assume x l Hir;
      apply ∧ᵢ
      { assume H; apply ∨ᶜₑ H
        {
          assume Hx;
          apply ∨ᶜᵢ₁;
          apply ∨ᶜᵢ₁;
          apply Hx;
        }
        {
          assume Hl++b;
          have tmp: π ((x ∨ᶜ (⟇_to_∨ᶜ_rw l ∨ᶜ ⟇_to_∨ᶜ_rw b))  ⇒ ((x ∨ᶜ ⟇_to_∨ᶜ_rw l) ∨ᶜ ⟇_to_∨ᶜ_rw b)) {
            refine ∧ₑ₁ ∨ᶜ_assoc;
          };
          apply tmp;
          apply ∨ᶜₑ H
          {
            assume Hx;  apply ∨ᶜᵢ₁; apply Hx
          }
          {
            assume Hl_or_b;
            apply ∨ᶜᵢ₂;
            have HirLeft: π ((⟇_to_∨ᶜ_rw (l ++ b) ⇒ (⟇_to_∨ᶜ_rw l ∨ᶜ ⟇_to_∨ᶜ_rw b))) {
                refine (∧ₑ₁ Hir);
            };
            apply HirLeft;
            apply Hl++b
          }
        }
      }
      {
        assume H;
        apply ∨ᶜₑ H {
            assume H1;
            apply ∨ᶜₑ H1 {
              assume Hx;
              apply ∨ᶜᵢ₁;
              apply Hx;
            } {
              assume H2;
              apply ∨ᶜᵢ₂;
              have tmp: π (((⟇_to_∨ᶜ_rw l ∨ᶜ ⟇_to_∨ᶜ_rw b) ⇒ ⟇_to_∨ᶜ_rw (l ++ b))) {
                refine (∧ₑ₂ Hir);
              };
              apply tmp;
              apply ∨ᶜᵢ₁;
              apply H2
            }
        } {
          assume H1;
          apply ∨ᶜᵢ₂;
          have tmp: π (((⟇_to_∨ᶜ_rw l ∨ᶜ ⟇_to_∨ᶜ_rw b) ⇒ ⟇_to_∨ᶜ_rw (l ++ b))) {
                refine (∧ₑ₂ Hir);
              };
              apply tmp;
              apply ∨ᶜᵢ₂;
              apply H1
        }        
      }
    }
end;
 
injective symbol ∧ᶜ : Prop → Prop → Prop; notation ∧ᶜ infix right 10;
constant symbol ∧ᶜᵢ [p q] : π p → π q → π (p ∧ᶜ q);
symbol ∧ᶜₑ₁ [p q] : π (p ∧ᶜ q) → π p;
symbol ∧ᶜₑ₂ [p q] : π (p ∧ᶜ q) → π q;

injective symbol ⟹ᶜ: Prop → Prop → Prop;
notation ⟹ᶜ infix right 7;

constant symbol ⟹ᶜ_right [a b] : (π a → π b) → π (a ⟹ᶜ b);

constant symbol ⟹ᶜ_to_∨ᶜ [a b] : π (a ⟹ᶜ b) → π ((¬ᶜ a) ∨ᶜ b);

constant symbol ∨ᶜ_to_⟹ᶜ [a b] : π ((¬ᶜ a) ∨ᶜ b) → π (a ⟹ᶜ b);

injective symbol ⟺ᶜ: Prop → Prop → Prop;
notation ⟺ᶜ infix right 6;

constant symbol ⟺ᶜᵢ [p q] : (π p → π  q) →  (π q → π p) → π (p ⟺ᶜ q);

constant symbol ⟺ᶜₑ [p q r] : π (p ⟺ᶜ q) →  ((π p → π q) → (π q → π p) → π r) → π r;

opaque symbol ⟺ᶜ_refl [p] : π (p ⟺ᶜ p) ≔
begin
  assume p;
  apply ⟺ᶜᵢ
  {assume Hp; apply Hp}
  {assume Hp; apply Hp}
end;

opaque symbol ⟺ᶜ_sym [p q] : π (p ⟺ᶜ q) → π (q ⟺ᶜ p) ≔
begin
  assume p q Hp_equiv_q;
  apply ⟺ᶜᵢ
  {
    assume Hq;
    apply ⟺ᶜₑ Hp_equiv_q;
    assume Hpq Hqp;
    apply Hqp;
    apply Hq;
  }
  {
    assume Hp;
    apply ⟺ᶜₑ Hp_equiv_q;
    assume Hpq Hqp;
    apply Hpq;
    apply Hp;
  }
end;

opaque symbol ⟺ᶜ_trans [p q r] : π (p ⟺ᶜ q) → π (q ⟺ᶜ r) → π (p ⟺ᶜ r) ≔
begin
  assume p q r Hpq Hqr;
  apply ⟺ᶜᵢ
  {
    assume Hp;
    apply ⟺ᶜₑ Hpq;
    assume Hp_imp_q Hq_imp_p;
    apply ⟺ᶜₑ Hqr;
    assume Hq_imp_r Hr_imp_q;
    apply Hq_imp_r (Hp_imp_q Hp );
  }
  {
    assume Hr;
    apply ⟺ᶜₑ Hpq;
    assume Hp_imp_q Hq_imp_p;
    apply ⟺ᶜₑ Hqr;
    assume Hq_imp_r Hr_imp_q;
    apply Hq_imp_p (Hr_imp_q Hr );
  };
end;

opaque symbol feq_equiv (f:τ o → τ o) [x x':τ o] : π(f x = f x') → π(f x ⟺ᶜ f x') ≔
begin
  assume f x x' Hfeq;
  rewrite Hfeq;
  apply ⟺ᶜ_refl
end;

// axiom Prop equality is equivalent to x equivalent  
constant symbol eq_equiv [x y: Prop]: π (x ⟺ᶜ y) → π (x = y);

opaque symbol cong [x x'] (f: Prop → Prop): π(x ⟺ᶜ x') → π(f x ⟺ᶜ f x') ≔
begin
  assume x y f Hequivxy;
  rewrite eq_equiv Hequivxy;
  apply ⟺ᶜ_refl
end;

opaque symbol cong2 [x y x' y'] (f: Prop → Prop → Prop): π (x ⟺ᶜ x') → π (y ⟺ᶜ y') → π((f x y) ⟺ᶜ (f x' y')) ≔
begin
  assume x x' y y' f Hequivxx' Hequivyy';
  rewrite eq_equiv Hequivxx';
  rewrite eq_equiv Hequivyy';
  apply ⟺ᶜ_refl
end;

constant symbol ∀ᶜ [a] : (τ a → Prop) → Prop; notation ∀ᶜ quantifier;
constant symbol ∀ᶜᵢ [p] : (Π x, π (p x)) → π (∀ᶜ p);
constant symbol ∀ᶜₑ [p] x : π (∀ᶜ p) → π (p x);

constant symbol ∃ᶜ [a] : (τ a → Prop) → Prop; notation ∃ᶜ quantifier;
constant symbol ∃ᶜᵢ [a] p (x:τ a) : π (p x) → π (∃ᶜ p);
symbol ∃ᶜₑ [a] p : π (∃ᶜ p) → Π q, (Π x:τ a, π (p x) → π q) → π q;

rule ∃ᶜₑ _ (∃ᶜᵢ _ $x $px) _ $f ↪ $f $x $px;

constant symbol classic [p] : π (p ∨ᶜ ¬ᶜ p);

constant symbol nnpp [p] : π (¬ᶜ ¬ᶜ p) → π p;

//TODO: Need classical definition
opaque symbol pnnp [p] : π p → π (¬ᶜ ¬ᶜ p) ≔
begin admit end;

constant symbol ⟹ᶜᵢ [p q] : (π p → π q) → π (p ⟹ᶜ q);

constant symbol ⟹ᶜₑ [p q] : π (p ⟹ᶜ q) → π p → π q;

constant symbol imply_to_or[p q] : π (p ⟹ᶜ q) → π ((¬ᶜ p) ∨ᶜ q);

constant symbol imply_to_and [p q] : π (¬ᶜ (p ⟹ᶜ q)) → π (p ∧ᶜ (¬ᶜ q));

// Hilbert epsilon operator/choice
constant symbol ϵ  [a]: (τ a → Prop) → τ a; notation ϵ quantifier;

constant symbol ϵᵢ x p : π (p x) → π (p (ϵ p));
constant symbol ϵ_det [p q]: Π x, π ((p x) ⟺ᶜ (q x)) → π (ϵ p = ϵ q);

opaque symbol ϵ_equiv_∃ᶜ [p] : π ((`∃ᶜ x, p x) ⟺ᶜ (p (`ϵ x, p x))) ≔
begin
  assume p;
  apply ⟺ᶜᵢ
  {
    assume Hexist;
    apply ∃ᶜₑ _ Hexist;
    assume x Hpx;
    apply ϵᵢ x (λ u, p u);
    apply Hpx
  }
  {
    assume Heps;
    apply ∃ᶜᵢ _ (`ϵ x, p x);
    apply Heps
  } 
end;

symbol ite c t e ≔ (c ⟹ᶜ t) ∧ᶜ (¬ᶜ c ⟹ᶜ e);
constant symbol iteI : Π c t e p,
                           (π c → π (p t))
                         → ((π c → π ⊥) → π (p e))
                         → π (p (ite c t e));                         

opaque symbol ∨ᶜ_to_⟇ a b: π (a ∨ᶜ b) → π̇ (a ⟇ b ⟇ ▩) ≔
begin
  assume a b Haorb;
  apply ∨ᶜₑ Haorb
  { assume Ha;  apply ∨ᶜᵢ₁; apply Ha }
  {  assume Hb; apply ∨ᶜᵢ₂; simplify; apply ∨ᶜᵢ₁; apply Hb }
end; 

opaque symbol ite1 [c t e] : π (ite c t e) → π̇ (c ⟇ e ⟇ ▩) ≔
begin
  assume c t e Hite;
  apply ∨ᶜ_to_⟇;
  have H: π (¬ᶜ c ⟹ᶜ e) { apply ∧ᶜₑ₂ Hite }; 
  have tmp: π (c ∨ᶜ e ⟺ᶜ  (¬ᶜ ¬ᶜ c) ∨ᶜ e) { 
    apply ⟺ᶜᵢ
    {
      assume H1;
      apply ∨ᶜₑ H1
      { assume Hc; apply ∨ᶜᵢ₁; apply pnnp; apply Hc }
      { assume He; apply ∨ᶜᵢ₂;  apply He };
    }
    {
      assume H1; 
      apply ∨ᶜₑ H1
      { assume Hc; apply ∨ᶜᵢ₁; apply nnpp; apply Hc }
      { assume He; apply ∨ᶜᵢ₂;  apply He };
    };
  };
  apply ⟺ᶜₑ tmp;
  assume H1 H2;
  apply H2;
  apply ⟹ᶜ_to_∨ᶜ;
  apply H
end;

opaque symbol ite2 [c t e] : π (ite c t e) → π̇ ((¬ᶜ c) ⟇ t ⟇ ▩) ≔
begin
  assume c t e Hite;
  apply ∨ᶜ_to_⟇;
  have H: π (c ⟹ᶜ t) { apply ∧ᶜₑ₁ Hite };
  apply ⟹ᶜ_to_∨ᶜ;
  apply H
end;

opaque symbol ite_pos1 [c t e] : π̇ (¬ᶜ (ite c t e) ⟇ c ⟇ e ⟇ ▩) ≔
begin
  assume c t e;
  apply ⟹ᶜ_to_∨ᶜ;
  apply ⟹ᶜᵢ;
  assume H;
  apply ite1 H;
end;

opaque symbol ite_pos2 [c t e] : π̇ (¬ᶜ (ite c t e) ⟇ ¬ᶜ c ⟇ t ⟇ ▩) ≔
begin
  assume c t e;
  apply ⟹ᶜ_to_∨ᶜ;
  apply ⟹ᶜᵢ;
  assume H;
  apply ite2 H;
end;

opaque symbol ite_neg1 [c t e] : π̇ ((ite c t e) ⟇ c ⟇ ¬ᶜ e ⟇ ▩) ≔
begin
  admit
end;

opaque symbol ite_neg2 [c t e] : π̇ ((ite c t e) ⟇ ¬ᶜ c ⟇ ¬ᶜ t ⟇ ▩) ≔
begin
  admit
end;

opaque symbol not_ite1 [c t e] : π (¬ᶜ (ite c t e)) → π̇( c ⟇ ¬ᶜ e ⟇ ▩) ≔
begin
  assume c t e H;
  admit
end;

opaque symbol not_ite2 [c t e] : π (¬ᶜ (ite c t e)) → π̇(¬ᶜ c ⟇ ¬ᶜ t ⟇ ▩) ≔
begin
  assume c t e H;
  admit
end;

symbol xor a b ≔ ((¬ᶜ a) ∧ᶜ b) ∨ᶜ (a ∧ᶜ (¬ᶜ b));

opaque symbol xor_pos1 [a b] : π̇ (¬ᶜ (xor a b) ⟇ a ⟇ b ⟇ ▩) ≔
begin
  assume a b;
  simplify;
  apply ⟹ᶜ_to_∨ᶜ;
  apply ⟹ᶜᵢ;
  assume H;
  apply ∨ᶜₑ H
  { assume Hnab; apply ∨ᶜᵢ₂;  apply ∨ᶜᵢ₁; apply ∧ᶜₑ₂ Hnab }
  { assume Hnab; apply ∨ᶜᵢ₁; apply ∧ᶜₑ₁ Hnab }
end;

opaque symbol xor_pos2 [a b] : π̇ (¬ᶜ (xor a b) ⟇ ¬ᶜ a ⟇ ¬ᶜ b ⟇ ▩) ≔
begin
  assume a b;
  simplify;
  apply ⟹ᶜ_to_∨ᶜ;
  apply ⟹ᶜᵢ;
  assume H;
  apply ∨ᶜₑ H
  { assume Hnab; apply ∨ᶜᵢ₁; apply ∧ᶜₑ₁ Hnab }
  { assume Hnab; apply ∨ᶜᵢ₂;  apply ∨ᶜᵢ₁; apply ∧ᶜₑ₂ Hnab }
end;

opaque symbol xor_neg1 [a b] : π̇ ((xor a b) ⟇ a ⟇ ¬ᶜ b ⟇ ▩) ≔
begin
  simplify;
  admit
end;

opaque symbol xor_neg2 [a b] : π̇ ((xor a b) ⟇ ¬ᶜ a ⟇ b ⟇ ▩) ≔
begin
  admit
end;

symbol trivial : π ⊤;

symbol neg_true : π (¬ᶜ ⊥);

// i ▷ 𝜑1 ∨ ⋯ ∨ 𝜑n
// j ▷ 𝜑1 , ⋯ , 𝜑n
//constant symbol or [a b] : π̇ ((a ∨ᶜ b) ⟇ ▩) → π̇ (∨ᶜ_to_⟇_rw  (a ∨ᶜ b));

opaque symbol not_not x : π̇ ( (¬ᶜ (¬ᶜ (¬ᶜ x))) ⟇ x ⟇ ▩) ≔
begin
  assume x;
  apply ⟹ᶜ_to_∨ᶜ;
  apply ⟹ᶜᵢ;
  assume H;
  apply ∨ᶜᵢ₁;
  apply nnpp H
end;

opaque symbol implies [φ₁ φ₂] : π (φ₁ ⟹ᶜ φ₂) → π̇ (¬ᶜ φ₁ ⟇ φ₂ ⟇ ▩) ≔
begin
  assume φ₁ φ₂ Hφ₁⟹ᶜφ₂;
  apply ⟹ᶜ_to_∨ᶜ;
  apply ⟹ᶜᵢ;
  assume πφ₁;
  apply ∨ᶜᵢ₁;
  apply ⟹ᶜₑ Hφ₁⟹ᶜφ₂ πφ₁
end;

opaque symbol not_implies1 [φ₁ φ₂] : π (¬ᶜ (φ₁ ⟹ᶜ φ₂)) → π̇ (φ₁ ⟇ ▩) ≔
begin
  assume φ₁ φ₂ Hnot_φ₁⟹ᶜφ₂;
  apply ∨ᶜᵢ₁;
  apply ∧ᶜₑ₁ (imply_to_and Hnot_φ₁⟹ᶜφ₂)
end;

opaque symbol not_implies2 [φ₁ φ₂] : π (¬ᶜ (φ₁ ⟹ᶜ φ₂)) →  π̇ (¬ᶜ φ₂ ⟇ ▩) ≔
begin
  assume φ₁ φ₂ Hnot_φ₁⟹ᶜφ₂;
  apply ∨ᶜᵢ₁;
  apply ∧ᶜₑ₂ (imply_to_and Hnot_φ₁⟹ᶜφ₂)
end;

opaque symbol implies_neg1 [φ₁ φ₂] : π̇ (φ₁ ⟹ᶜ φ₂ ⟇ φ₁ ⟇ ▩) ≔
begin
  assume φ₁ φ₂;
  have Hassoc: π (((φ₁ ⟹ᶜ φ₂) ∨ᶜ (φ₁ ∨ᶜ ⊥)) ⇔ (((φ₁ ⟹ᶜ φ₂) ∨ᶜ φ₁) ∨ᶜ ⊥)) {
    apply ∨ᶜ_assoc
  };
  have Lassoc: π ((((φ₁ ⟹ᶜ φ₂) ∨ᶜ φ₁) ∨ᶜ ⊥) ⇒ ((φ₁ ⟹ᶜ φ₂) ∨ᶜ (φ₁ ∨ᶜ ⊥))) {
    apply ∧ₑ₂ Hassoc;
  };
  apply Lassoc;
  apply ∨ᶜᵢ₁;
  admit //FIXME: finish the proof with ⟹ᶜ_to_∨ᶜ and EM
end;

constant symbol implies_neg2 [φ₁ φ₂] : π̇ (φ₁ ⟹ᶜ φ₂ ⟇ ¬ᶜ φ₂ ⟇ ▩);

opaque symbol equiv1 [φ₁ φ₂] : π̇ (φ₁ ⟺ᶜ φ₂ ⟇ ▩) → π̇ ((¬ᶜ φ₁) ⟇ φ₂ ⟇ ▩) ≔
begin
  assume φ₁ φ₂ H1;
  apply ∨ᶜₑ H1
  {
    assume Hequiv;
    apply ⟺ᶜₑ Hequiv;
    assume H2 H3;
    simplify;
    have Hassoc: π (((¬ᶜ φ₁) ∨ᶜ (φ₂ ∨ᶜ ⊥)) ⇔ (((¬ᶜ φ₁) ∨ᶜ φ₂) ∨ᶜ ⊥)) {
      apply (@∨ᶜ_assoc (¬ᶜ φ₁) φ₂ ⊥);
    };
    have Hassoc_left: π ((((¬ᶜ φ₁) ∨ᶜ φ₂) ∨ᶜ ⊥)  ⇒  ((¬ᶜ φ₁) ∨ᶜ (φ₂ ∨ᶜ ⊥))) {
      refine ∧ₑ₂ Hassoc
    };
    apply Hassoc_left;
    apply ∨ᶜᵢ₁;
    apply ⟹ᶜ_to_∨ᶜ;
    apply ⟹ᶜᵢ;
    refine H2;
  }
  {
    assume Hbot;
    apply ∨ᶜᵢ₂;
    apply ∨ᶜᵢ₂;
    apply Hbot;
  }
end;

opaque symbol equiv2 [φ₁ φ₂] : π̇ (φ₁ ⟺ᶜ φ₂ ⟇ ▩)  → π̇ (φ₁ ⟇ (¬ᶜ φ₂) ⟇ ▩) ≔
begin
  assume φ₁ φ₂ H1;
  apply ∨ᶜₑ H1
  {
    assume Hequiv;
    apply ⟺ᶜₑ Hequiv;
    assume H2 H3;
    simplify;
    have Hassoc: π ((φ₁ ∨ᶜ ((¬ᶜ φ₂) ∨ᶜ ⊥)) ⇔ ((φ₁ ∨ᶜ (¬ᶜ φ₂)) ∨ᶜ ⊥)) {
      apply (@∨ᶜ_assoc φ₁ (¬ᶜ φ₂) ⊥);
    };
    have Hassoc_left: π (((φ₁ ∨ᶜ (¬ᶜ φ₂)) ∨ᶜ ⊥)  ⇒  (φ₁ ∨ᶜ ((¬ᶜ φ₂) ∨ᶜ ⊥))) {
      refine ∧ₑ₂ Hassoc
    };
    apply Hassoc_left;
    apply ∨ᶜᵢ₁;
    apply ∨ᶜ_com;
    apply ⟹ᶜ_to_∨ᶜ;
    apply ⟹ᶜᵢ;
    refine H3;
  }
  {
    assume Hbot;
    apply ∨ᶜᵢ₂;
    apply ∨ᶜᵢ₂;
    apply Hbot;
  }
end;

constant symbol equiv_pos1 [φ₁ φ₂] : π̇ ((¬ᶜ (φ₁ ⟺ᶜ φ₂)) ⟇ φ₁ ⟇ ¬ᶜ φ₂ ⟇ ▩);

constant symbol equiv_pos2 [φ₁ φ₂] : π̇ ((¬ᶜ (φ₁ ⟺ᶜ φ₂)) ⟇ (¬ᶜ φ₁) ⟇ φ₂ ⟇ ▩);

constant symbol equiv_neg1 [φ₁ φ₂] : π̇ ((φ₁ ⟺ᶜ φ₂) ⟇ ¬ᶜ φ₁ ⟇ ¬ᶜ φ₂ ⟇ ▩);

constant symbol equiv_neg2 [φ₁ φ₂] : π̇ ((φ₁ ⟺ᶜ φ₂) ⟇ φ₁ ⟇ φ₂ ⟇ ▩);

constant symbol implies_pos [φ₁ φ₂] : π̇ ((¬ᶜ (φ₁ ⟹ᶜ φ₂)) ⟇ ¬ᶜ φ₁ ⟇ φ₂ ⟇ ▩);

opaque symbol subproof1 [φ₁ ψ] : π φ₁ → π ψ → π̇ ((¬ᶜ φ₁) ⟇ ψ ⟇ ▩) ≔
begin
  assume φ₁ ψ Hφ₁ Hψ;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₁;
  apply Hψ
end;

opaque symbol subproof2 [φ₁ φ₂ ψ] : π φ₁ → π φ₂ → π ψ → π̇ ((¬ᶜ φ₁) ⟇ (¬ᶜ φ₂) ⟇ ψ ⟇ ▩) ≔
begin
  assume φ₁ φ₂ ψ Hφ₁ Hφ₂ Hψ;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₁;
  apply Hψ;
end;

opaque symbol subproof3 [φ₁ φ₂ φ₃ ψ] : π φ₁ → π φ₂ → π φ₃ → π ψ → π̇ ((¬ᶜ φ₁) ⟇ (¬ᶜ φ₂) ⟇ (¬ᶜ φ₃) ⟇ ψ ⟇ ▩) ≔
begin
  assume φ₁ φ₂ φ₃ ψ Hφ₁ Hφ₂ Hφ₃ Hψ;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₁;
  apply Hψ;
end;

opaque symbol subproof4 [φ₁ φ₂ φ₃ φ₄ ψ] : π φ₁ → π φ₂ → π φ₃ → π φ₄ → π ψ → π̇ ((¬ᶜ φ₁) ⟇ (¬ᶜ φ₂) ⟇ (¬ᶜ φ₃) ⟇ (¬ᶜ φ₄) ⟇ ψ ⟇ ▩) ≔
begin
  assume φ₁ φ₂ φ₃ φ₄ ψ Hφ₁ Hφ₂ Hφ₃ Hφ₄ Hψ;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₁;
  apply Hψ;
end;

constant symbol forall_inst1 p x: π (¬ᶜ (`∀ᶜ x', p x') ∨ᶜ (p x));

constant symbol forall_inst2 p x y: π (¬ᶜ (`∀ᶜ a, `∀ᶜ b, p a b) ∨ᶜ (p x y));

opaque symbol forall_inst3 [p] x y z: π ((¬ᶜ (`∀ᶜ a, `∀ᶜ b, `∀ᶜ c, p a b c)) ∨ᶜ ((p x y z) ∨ᶜ ⊥)) ≔
begin
  assume p x y z;
  apply imply_to_or;
  apply ⟹ᶜᵢ;
  assume H;
  apply ∨ᶜᵢ₁ (∀ᶜₑ z (∀ᶜₑ y (∀ᶜₑ x H)))
end;

print forall_inst3;

// symbol morgan [p q] : π (¬ᶜ (p ∨ᶜ q)) → π (¬ᶜ p ∧ᶜ ¬ᶜ q);

// sequential symbol morgan_l: Prop → Prop;
// sequential symbol ∧_to_∨: Prop → Prop;

// rule morgan_l  (¬ᶜ $hd) ∧ᶜ $tl ↪ ¬ᶜ ( $hd ∨ᶜ (∧_to_∨  $tl));
// rule ∧_to_∨ (¬ᶜ $hd) ∧ᶜ $tl ↪ $hd ∨ᶜ (∧_to_∨ $tl)
// with ∧_to_∨ ⊤ ↪ ⊤;

// sequential symbol morgan_r: Prop → Prop;
// sequential symbol ⟇_to_∧: Prop → Prop;

// rule morgan_r  ¬ᶜ ($hd ∨ᶜ $tl) ↪ ¬ᶜ $hd ∧ᶜ (⟇_to_∧ $tl);
// rule ⟇_to_∧ ($a ∨ᶜ $b) ↪  ¬ᶜ $a ∧ᶜ (⟇_to_∧ $b)
// with ⟇_to_∧ ⊥ ↪ ⊤;

// # In Predicate
// 
// The In predicate works with 𝔹 instead of Prop to avoid making critical pairs wiht other rules.
// If we use Prop, then we will need a rule
// ▷ `$x ⟺ᶜ $x ↪ ⊤` to replace `eq $x $h` and, 
// ▷ `_ ∨ᶜ ⊤ ↪ ⊤` for `or _ true ↪ true`. 
//
// This choice will create a critical pair reduction which would make any clause in the goal
// that contain the litteral ⊤ unable to compute the predicate In.
//
// To illustrate this case, consider the goal:
// ⊢ (𝜑1 ∨ᶜ ⋯ ∨ᶜ ⊤ ⋯ ∨ᶜ 𝜑𝑛), ¬𝜑k
// then we will have
// ⊢ In_∨ᶜ 𝜑k (𝜑1 ∨ᶜ ⋯ ∨ᶜ ⊤ ⋯ ∨ᶜ 𝜑𝑛)  (apply or_neg)
// ⊢ In_∨ᶜ 𝜑k ⊤  (by simplification)
// we got stuck...


symbol 𝑰 [a]: ℕ → τ a; 
symbol code_S : Set;
symbol S ≔ τ code_S;
symbol a: Prop ≔ 𝑰 0;

symbol b: Prop ≔ 𝑰 1;
symbol c: Prop ≔ 𝑰 2;
symbol d: Prop ≔ 𝑰 3;
symbol e: Prop ≔ 𝑰 4;

// Decidable equality in 𝔹.
// Symbol = has been declared constant, it cannot be used as the head of a rewrite rule LHS.
// So we create our own eq symbol.
symbol eq [a]: τ a → τ a → 𝔹;
// constant symbol ind_eq [a] : Π p0: (𝔹 → Prop), π (p0 true) → π (p0 false) → Π x, Π y: τ a, π (p0 (eq x y));

rule eq (𝑰 0) (𝑰 0) ↪ true
with eq (@𝑰 $a ($x +1)) (@𝑰 $b ($y +1)) ↪ eq (@𝑰 $a $x) (@𝑰 $b $y)
with eq (𝑰 0) (𝑰 (_ +1)) ↪ false
with eq (𝑰 (_ +1)) (𝑰 0) ↪ false;

// and_neg:  (𝜑1 ∧ ⋯ ∧ 𝜑𝑛), ¬𝜑1, … , ¬𝜑𝑛
symbol and_neg_r: Prop → Clause → 𝔹; 
rule and_neg_r ⊥ (_ ⟇ _) ↪ false
with and_neg_r ⊤ (_ ⟇ _) ↪ false
with and_neg_r (¬ᶜ _) (_ ⟇ _) ↪ false
with and_neg_r (_ ∨ᶜ _) (_ ⟇ _) ↪ false
with and_neg_r ($x ∧ᶜ _) (⊥ ⟇ _) ↪ if (eq $x ⊥) true false
with and_neg_r ($x ∧ᶜ _) (⊤ ⟇ _) ↪ if (eq $x ⊤) true false
with and_neg_r ($x ∧ᶜ _) ((_ ∨ᶜ _) ⟇ _) ↪ false
with and_neg_r ($x ∧ᶜ _) ((_ ∧ᶜ _) ⟇ _) ↪ false
with and_neg_r ($x ∧ᶜ $tl) (¬ᶜ $y ⟇ $tl2) ↪ if (eq $x $y)  (and_neg_r $tl $tl2) false
with and_neg_r ⊥ ▩ ↪ false
with and_neg_r (_ ∧ᶜ _) ▩ ↪ false
with and_neg_r (_ ∨ᶜ _) ▩ ↪ false
with and_neg_r (¬ᶜ _) ▩ ↪ false
with and_neg_r ⊤ ▩ ↪ true;

//constant symbol ifₑ c t e p : π (p (if c t e)) → π (¬ c) → π (p e);

// opaque symbol iteE c t e p : Prf (p (ite c t e)) → Prf (¬ c) → Prf (p e) ≔
// {  apply iteE q true false (λ z, z) qite pnq };

symbol and_neg [l1 l2]: π (and_neg_r l1 l2 = true) → π̇ (l1 ⟇ l2);

symbol ind_Prop :
Π p: (Prop → Prop),
π (p ⊤) →
π (p ⊥) →
(Π x: Prop, π (p x) → π (p (¬ᶜ x))) →
(Π x: Prop, π (p x) → Π y: Prop, π (p y) → π (p (x ∧ᶜ y))) →
(Π x: Prop, π (p x) → Π y: Prop, π (p y) → π (p (x ∨ᶜ y))) →
Π x: Prop, π (p x);


symbol and_neg_proof [l1 l2] : π (and_neg_r l1 l2 = true ⟹ᶜ (l1 ∨ᶜ ⟇_to_∨ᶜ_rw l2)) ≔
begin
  assume l1 l2;
  apply ind_Prop (λ l1', and_neg_r l1' l2 = true ⟹ᶜ ⟇_to_∨ᶜ_rw (l1' ⟇ l2))
  {
    apply Clause_ind (λ l2', (and_neg_r ⊤ l2' = true) ⟹ᶜ ⟇_to_∨ᶜ_rw (⊤ ⟇ l2')) l2
    {
      apply ⟹ᶜᵢ;
      assume HReflTrue;
      apply ∨ᶜᵢ₁;
      apply trivial
    }
    {
      assume x l2' IH; simplify; apply ⟹ᶜᵢ; assume HfalseEqTrue; apply ⊥ₑ; apply false≠true HfalseEqTrue
    }
  }
  {
    admit
  }
  {
    admit
  }
  {
    assume x Hx y Hy;
    apply Clause_ind (λ l2', (and_neg_r (x ∧ᶜ y) l2' = true) ⟹ᶜ ⟇_to_∨ᶜ_rw ((x ∧ᶜ y) ⟇ l2')) l2
    { admit }
    {
      assume x' l2' IHClause;
      apply ind_Prop (λ u, (and_neg_r (x ∧ᶜ y) (u ⟇ l2') = true) ⟹ᶜ ⟇_to_∨ᶜ_rw ((x ∧ᶜ y) ⟇ (u ⟇ l2')))
      { admit }
      { admit }
      { 
        assume x1 IHProp;
        simplify;
        apply ind_𝔹_eq (λ u, ((if (u) (and_neg_r y l2') false) = true) ⟹ᶜ ((x ∧ᶜ y) ∨ᶜ ((¬ᶜ x1) ∨ᶜ (⟇_to_∨ᶜ_rw l2')))) (eq x x1)
        {
          assume Htrue;
          rewrite Htrue;
          simplify;
          apply ⟹ᶜᵢ;
          assume H2;
          admit
        }
        {
          assume HEqfalse;
          rewrite HEqfalse;
          simplify;
          apply ⟹ᶜᵢ;
          assume HfalseEqTrue;
          apply ⊥ₑ;
          apply false≠true HfalseEqTrue;
        };
      }
      { admit }
      { admit }
    }
  }
  {
    admit
  }
end;

opaque symbol test_and_neg: π̇ ((a ∧ᶜ b ∧ᶜ c ∧ᶜ d ∧ᶜ ⊤) ⟇ ¬ᶜ a ⟇ ¬ᶜ b ⟇ ¬ᶜ c ⟇ ¬ᶜ d ⟇ ▩) ≔
begin
  apply and_neg; reflexivity
end; 



sequential symbol In_∧ᶜ: Prop → Prop → 𝔹;
rule In_∧ᶜ $x ($h ∧ᶜ $tl) ↪ (eq $x $h)  Stdlib.Bool.or (In_∧ᶜ $x $tl)
with In_∧ᶜ $x ⊤ ↪ false;

sequential symbol In_∨ᶜ: Prop → Prop → 𝔹;
rule In_∨ᶜ $x ($h ∨ᶜ $tl) ↪ (eq $x $h) Stdlib.Bool.or (In_∨ᶜ $x $tl)
with In_∨ᶜ _ ⊥ ↪ false;

// and_pos: ¬(𝜑1 ∧ … ∧ 𝜑𝑛), 𝜑𝑘
symbol and_pos [φ₁__φₙ φₖ]:  π ((In_∧ᶜ φₖ φ₁__φₙ) = true) → π̇ (¬ᶜ φ₁__φₙ ⟇ φₖ ⟇ ▩);

opaque symbol test_and_pos: π̇ ((¬ᶜ (a ∧ᶜ b ∧ᶜ c ∧ᶜ d ∧ᶜ ⊤)) ⟇ d ⟇ ▩) ≔
begin
  apply and_pos;
  reflexivity;
end; 



// or_pos:  ¬(𝜑1 ∨ ⋯ ∨ 𝜑𝑛), 𝜑1 , … , 𝜑𝑛
sequential symbol or_pos_r: Prop → Clause → 𝔹; 
rule or_pos_r ($x ∨ᶜ $tl) ($x ⟇ $tl2) ↪ or_pos_r $tl $tl2
with or_pos_r ⊥ ▩ ↪ true; 

symbol or_pos [l1 l2]: π (or_pos_r l1 l2 = true) → π̇ (¬ᶜ l1 ⟇ l2);

opaque symbol test_or_pos: π̇ (¬ᶜ (a ∨ᶜ b ∨ᶜ c ∨ᶜ d ∨ᶜ ⊥) ⟇ a ⟇ b ⟇ c ⟇ d ⟇ ▩) ≔
begin
  apply or_pos; reflexivity
end; 

// or_neg:
// i. ▷ (𝜑1 ∨ ⋯ ∨ 𝜑𝑛), ¬𝜑k
symbol or_neg [φ₁__φₙ] φₖ:  π ((In_∨ᶜ φₖ φ₁__φₙ) = true) → π̇ (φ₁__φₙ ⟇ ¬ᶜ φₖ ⟇ ▩);

opaque symbol test_or_neg: π̇ (((a ∨ᶜ b ∨ᶜ c ∨ᶜ d ∨ᶜ ⊥)) ⟇ ¬ᶜ c ⟇ ▩) ≔
begin
  apply or_neg; reflexivity
end; 

// not_or:
// i. ▷ ¬(𝜑1 ∨ ⋯ ∨ 𝜑𝑛)
// j. ▷ ¬𝜑𝑘
symbol not_or [φₖ] φ₁__φₙ: π (¬ᶜ φ₁__φₙ) → π ((In_∨ᶜ φₖ φ₁__φₙ) = true) → π̇ (¬ᶜ φₖ ⟇ ▩);

opaque symbol identity_⊥ [x] : π (x ∨ᶜ ⊥) → π x ≔
begin
  assume x H;
  apply ∨ᶜₑ H
  { assume Hx; apply Hx } { assume H⊥; apply ⊥ₑ; apply H⊥ }
end;

opaque symbol test_not_or: π̇ (¬ᶜ (a ∨ᶜ b ∨ᶜ c ∨ᶜ d ∨ᶜ ⊥) ⟇ ▩) → π̇ (¬ᶜ c ⟇ ▩) ≔
begin
  assume H; // i
  apply not_or (a ∨ᶜ b ∨ᶜ c ∨ᶜ d ∨ᶜ ⊥)
    { apply π̇ₗ; apply H }
    { reflexivity }
end;

// not_and:
// i. ▷ ¬(𝜑1 ∧ … ∧ 𝜑𝑛)
// j. ▷ ¬𝜑1, … , ¬𝜑𝑛
sequential symbol not_and_r: Prop → Clause → 𝔹; 
rule not_and_r ($x ∧ᶜ $tl) (¬ᶜ $x ⟇ $tl2) ↪ not_and_r $tl $tl2
with not_and_r ⊤ ▩ ↪ true; 

symbol not_and [l1 l2]: π (¬ᶜ l1) → π (not_and_r l1 l2 = true) → π̇ l2;

opaque symbol test_not_and: π̇ (¬ᶜ (a ∧ᶜ b ∧ᶜ c ∧ᶜ d ∧ᶜ ⊤) ⟇ ▩) → π̇ (¬ᶜ a ⟇ ¬ᶜ b ⟇ ¬ᶜ c ⟇ ¬ᶜ d ⟇ ▩) ≔
begin
  assume t1;
  apply not_and (π̇ₗ t1);
  reflexivity
end; 

// and:
// i. ▷ (𝜑1 ∧ ⋯ ∧ 𝜑𝑛)
// j. ▷ 𝜑𝑘
symbol and [φₖ] φ₁__φₙ : π ((In_∧ᶜ φₖ φ₁__φₙ) = true) → π̇ (φ₁__φₙ ⟇ ▩)  → π̇ (φₖ ⟇ ▩);

opaque symbol test_and:  π̇ ((a ∧ᶜ b ∧ᶜ c ∧ᶜ ⊤) ⟇ ▩) →  π̇ (c ⟇ ▩) ≔
begin
  assume t1;
  apply and ((a ∧ᶜ b ∧ᶜ c ∧ᶜ ⊤)) { reflexivity } { apply t1  };
end;

opaque symbol resolutionₗ x a b: π̇ (x ⟇ a) → π̇ ((¬ᶜ x) ⟇ b) → π̇ (a ++ b) ≔ begin
  assume x a b H1 H2;
  apply ⟇ₑ H1 {
    assume Hx;
    apply ⟇ₑ H2 {
      assume Hnx;
      simplify;
      have tmp:  π ((⟇_to_∨ᶜ_rw a ∨ᶜ ⟇_to_∨ᶜ_rw b)  ⇒ ⟇_to_∨ᶜ_rw (a ++ b)) {
        apply ∧ₑ₂ (++_to_∨ᶜ a b);
      };
      apply tmp;
      apply ∨ᶜₑ Hx { assume Hpi_x;  apply ∨ᶜₑ Hnx { assume Hpi_nx;  apply ¬ᶜₑ Hpi_nx Hpi_x }  {  assume Hbot; apply ⊥ₑ;  apply Hbot  } } { assume Hbot; apply ⊥ₑ;  apply Hbot  };
    } {
      assume Hb;
      have tmp:  π ((⟇_to_∨ᶜ_rw a ∨ᶜ ⟇_to_∨ᶜ_rw b)  ⇒ ⟇_to_∨ᶜ_rw (a ++ b)) {
        apply ∧ₑ₂ (++_to_∨ᶜ a b);
      };
      apply tmp;
      apply ∨ᶜᵢ₂;
      apply Hb;
    }
  } {
    assume Ha;
    apply ⟇ₑ H2 {
      assume Hnx;
      have tmp:  π ((⟇_to_∨ᶜ_rw a ∨ᶜ ⟇_to_∨ᶜ_rw b)  ⇒ ⟇_to_∨ᶜ_rw (a ++ b)) {
        apply ∧ₑ₂ (++_to_∨ᶜ a b);
      };
      apply tmp;
      apply ∨ᶜᵢ₁;
      apply Ha
    } {
      assume Hb;
      have tmp:  π ((⟇_to_∨ᶜ_rw a ∨ᶜ ⟇_to_∨ᶜ_rw b)  ⇒ ⟇_to_∨ᶜ_rw (a ++ b)) {
        apply ∧ₑ₂ (++_to_∨ᶜ a b);
      };
      apply tmp;
      apply ∨ᶜᵢ₁;
      apply Ha
    }
  };
end;

opaque symbol resolutionᵣ x a b: π̇ ((¬ᶜ x) ⟇ a) → π̇ (x ⟇ b) → π̇ (a ++ b) ≔ begin
  assume x a b H1 H2;
  apply ⟇ₑ H1 {
    assume Hnx;
    apply ⟇ₑ H2 {
      assume Hx;
      have tmp:  π ((⟇_to_∨ᶜ_rw a ∨ᶜ ⟇_to_∨ᶜ_rw b)  ⇒ ⟇_to_∨ᶜ_rw (a ++ b)) {
        apply ∧ₑ₂ (++_to_∨ᶜ a b);
      };
      apply tmp;
      apply ∨ᶜₑ Hx { assume Hpi_x;  apply ∨ᶜₑ Hnx { assume Hpi_nx;  apply ¬ᶜₑ Hpi_nx Hpi_x }  {  assume Hbot; apply ⊥ₑ;  apply Hbot  } } { assume Hbot; apply ⊥ₑ;  apply Hbot  };
    } {
      assume Hb;
      have tmp:  π ((⟇_to_∨ᶜ_rw a ∨ᶜ ⟇_to_∨ᶜ_rw b)  ⇒ ⟇_to_∨ᶜ_rw (a ++ b)) {
        apply ∧ₑ₂ (++_to_∨ᶜ a b);
      };
      apply tmp;
      apply ∨ᶜᵢ₂;
      apply Hb;
    }
  } {
    assume Ha;
    apply ⟇ₑ H2 {
      assume Hnx;
      have tmp:  π ((⟇_to_∨ᶜ_rw a ∨ᶜ ⟇_to_∨ᶜ_rw b)  ⇒ ⟇_to_∨ᶜ_rw (a ++ b)) {
        apply ∧ₑ₂ (++_to_∨ᶜ a b);
      };
      apply tmp;
      apply ∨ᶜᵢ₁;
      apply Ha
    } {
      assume Hb;
      have tmp:  π ((⟇_to_∨ᶜ_rw a ∨ᶜ ⟇_to_∨ᶜ_rw b)  ⇒ ⟇_to_∨ᶜ_rw (a ++ b)) {
        apply ∧ₑ₂ (++_to_∨ᶜ a b);
      };
      apply tmp;
      apply ∨ᶜᵢ₁;
      apply Ha
    }
  };
end;

opaque symbol bind_∃ [p q]: (Π x, π (p x ⟺ᶜ q x))  → π ((`∃ᶜ x, p x) ⟺ᶜ (`∃ᶜ x, q x)) ≔
begin
  assume p q H;
  apply ⟺ᶜᵢ 
  {
    assume H1;
    apply ∃ᶜₑ _ H1;
    assume x Hpx;
    apply ∃ᶜᵢ _ x;
    apply ⟺ᶜₑ (H x);
    assume Hpx_qx Hqx_px;
    apply Hpx_qx Hpx
  }
  {
    assume H1;
    apply ∃ᶜₑ _ H1;
    assume x Hqx;
    apply ∃ᶜᵢ _ x;
    apply ⟺ᶜₑ (H x);
    assume Hpx_qx Hqx_px;
    apply Hqx_px Hqx
  };
end;

opaque symbol bind_∀ [p q]: (Π x, π (p x ⟺ᶜ q x))  → π ((`∀ᶜ x, p x) ⟺ᶜ (`∀ᶜ x, q x)) ≔
begin
  assume p q H;
  apply ⟺ᶜᵢ 
  {
    assume H1;
    apply ∀ᶜᵢ _;
    assume x;
    have Hpx: π (p x) { apply ∀ᶜₑ x H1 };
    apply ⟺ᶜₑ (H x);
    assume Hpx_qx Hqx_px;
    apply Hpx_qx Hpx
  }
  {
    assume H1;
    apply ∀ᶜᵢ _;
    assume x;
    have Hqx: π (q x) { apply ∀ᶜₑ x H1 };
    apply ⟺ᶜₑ (H x);
    assume Hpx_qx Hqx_px;
    apply Hqx_px Hqx
  };
end;

symbol distinct [a] : 𝕃 a → Prop;