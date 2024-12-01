require open Stdlib.Prop;
require open Stdlib.FOL;
require open Stdlib.Set;
require open Stdlib.Eq;
require open Stdlib.Bool;
require open Stdlib.Nat;
require open lambdapi.Classic;

notation ¬ prefix 35;

// SMT use congruence of ⇔/= so we set `=` as infix right notation
// to be able to parse term such as `a = b = c`.
notation = infix right 10;

constant symbol eq_reflᶜ [a] (x:τ a) : πᶜ (x = x);
constant symbol ind_eqᶜ [a] [x y:τ a] : πᶜ (x = y) → Π p, πᶜ (p y) → πᶜ (p x);

//FIXME:
constant symbol meta-arr [p q]: (πᶜ p → πᶜ q) → πᶜ (p ⇒ q);

constant symbol fold_⇒ᶜ [p q] : πᶜ (p ⇒ q) → πᶜ p → πᶜ q;

builtin "P"     ≔ πᶜ; // : Prop → TYPE
builtin "refl"  ≔ eq_reflᶜ; // : Π [a] (x:T a), P(x = x)
builtin "eqind" ≔ ind_eqᶜ; // : Π [a] x y, P(x = y) → Π p:T a → Prop, P(p y) → P(p x)

symbol ⤳: Set → Set → Set; notation ⤳ infix right 20;
rule τ ($a ⤳ $b) ↪ τ $a →  τ $b;

// symbol ind_Prop :
// Π p: (Prop → Prop),
// πᶜ (p ⊤) →
// πᶜ (p ⊥) →
// (Π x: Prop, πᶜ (p x) → πᶜ (p (¬ x))) →
// (Π x: Prop, πᶜ (p x) → Π y: Prop, πᶜ (p y) → πᶜ (p (x ∧ᶜ y))) →
// (Π x: Prop, πᶜ (p x) → Π y: Prop, πᶜ (p y) → πᶜ (p (x ∨ᶜ y))) →
// Π x: Prop, πᶜ (p x);

// testing symbols
private symbol a: Prop;
private symbol b: Prop;
private symbol c: Prop;
private symbol d: Prop;
private symbol e: Prop;

symbol o: Set;
rule τ o ↪ Prop;

symbol Bool ≔ o;

// Index symbol for having a total equality function
injective symbol 𝑰 [a]: ℕ → τ a;

symbol trivial : πᶜ ⊤;

symbol neg_⊥ : πᶜ (¬ ⊥);

// # Clause
// Clauses are encoded with list à la Church Encoding.
// This encoding is necessary because Inductive type in Lambdapi
// could not live in Prop.
constant symbol Clause : TYPE;

constant symbol clause: Set;
rule τ clause ↪ Clause;

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
  πᶜ (P ▩) →
  (Π x: Prop, Π l: Clause, πᶜ (P l) → πᶜ (P (x ⟇ l))) →
  πᶜ (P l);

// some sanity checks
assert x y z ⊢ x ++ y ++ z ≡ x ++ (y ++ z);
assert x l m ⊢ x ⟇ l ++ m ≡ x ⟇ (l ++ m);


sequential symbol ∨ᶜ_to_⟇_rw: Prop → Clause;
rule ∨ᶜ_to_⟇_rw ($x ∨ᶜ $y) ↪ $x ⟇ (∨ᶜ_to_⟇_rw $y)
with ∨ᶜ_to_⟇_rw ⊥ ↪  ▩;

sequential symbol ⟇_to_∨ᶜ_rw: Clause → Prop;
rule ⟇_to_∨ᶜ_rw ($x ⟇ $y) ↪ $x ∨ᶜ (⟇_to_∨ᶜ_rw $y)
with ⟇_to_∨ᶜ_rw ▩ ↪ ⊥;

assert ⊢ ⟇_to_∨ᶜ_rw (a ⟇ b ⟇ ▩) ≡ a ∨ᶜ b ∨ᶜ ⊥;
assert ⊢ ∨ᶜ_to_⟇_rw (a ∨ᶜ b ∨ᶜ ⊥ ∨ᶜ c ∨ᶜ ⊥) ≡ (a ⟇ b ⟇ ⊥ ⟇ c ⟇ ▩);

injective symbol π̇ c: TYPE ≔ πᶜ (⟇_to_∨ᶜ_rw c);

opaque symbol π̇ₗ [a] : π̇ (a ⟇ ▩)  → πᶜ a ≔
begin
  assume a Hcl_a;
  apply @∨ᶜₑ a ⊥ a
  { apply Hcl_a }
  { assume Ha; apply Ha }
  { assume False; apply ⊥ᶜₑ False; };
end;

// opaque injective symbol πᶜ p : TYPE ≔ πᶜ (¬ (¬ p));

// Introduction rule for Clause
// construct `p ⟇ q` from a clause with only `p`
opaque symbol ⟇ᵢ₁ [p q] : π̇ (p ⟇ ▩) → π̇ (p ⟇ q) ≔
begin
  assume p q Hp;
  apply ∨ᶜₑ Hp
  { assume Hpi_p; apply ∨ᶜᵢ₁;  apply Hpi_p }
  { assume Hbot; apply ⊥ᶜₑ; apply Hbot }
end;

// construct `p ⟇ q` from a proof of `p`
opaque symbol ⟇ᵢ₁' [p q] : πᶜ p → π̇ (p ⟇ q) ≔
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


opaque symbol ++_to_∨ᶜ a b : πᶜ ((⟇_to_∨ᶜ_rw (a ++ b)) ⇔ᶜ  ((⟇_to_∨ᶜ_rw a) ∨ᶜ (⟇_to_∨ᶜ_rw b))) ≔
begin
  assume a b;
  apply Clause_ind (λ u, (⟇_to_∨ᶜ_rw (u ++ b)) ⇔ᶜ  ((⟇_to_∨ᶜ_rw u) ∨ᶜ (⟇_to_∨ᶜ_rw b))) a
    {
      apply ∧ᶜᵢ
        { apply ⇒ᶜᵢ; assume H; apply ∨ᶜᵢ₂; apply H }
        {
          apply ⇒ᶜᵢ; assume H; 
          apply ∨ᶜₑ H { assume H⊥; apply ⊥ᶜₑ; apply H⊥ } { assume H1;  apply H1}
        }
    }
    {
      assume x l Hir;
      apply ∧ᶜᵢ
      { apply ⇒ᶜᵢ; assume H;   apply ∨ᶜₑ H
        {
          assume Hx;
          apply ∨ᶜᵢ₁;
          apply ∨ᶜᵢ₁;
          apply Hx;
        }
        {
          assume Hl++b;
          have tmp: πᶜ ((x ∨ᶜ (⟇_to_∨ᶜ_rw l ∨ᶜ ⟇_to_∨ᶜ_rw b)) ⇒ᶜ ((x ∨ᶜ ⟇_to_∨ᶜ_rw l) ∨ᶜ ⟇_to_∨ᶜ_rw b)) {
            
            refine ∧ᶜₑ₁ ∨ᶜ_assoc;  //((x ∨ᶜ (⟇_to_∨ᶜ_rw l ∨ᶜ ⟇_to_∨ᶜ_rw b)) ⇒ᶜ ((x ∨ᶜ ⟇_to_∨ᶜ_rw l) ∨ᶜ ⟇_to_∨ᶜ_rw b))
          };
          apply ⇒ᶜₑ tmp;
          apply ∨ᶜₑ H
          {
            assume Hx;  apply ∨ᶜᵢ₁; apply Hx
          }
          {
            assume Hl_or_b;
            apply ∨ᶜᵢ₂;
            have HirLeft: πᶜ ((⟇_to_∨ᶜ_rw (l ++ b) ⇒ᶜ (⟇_to_∨ᶜ_rw l ∨ᶜ ⟇_to_∨ᶜ_rw b))) {
                refine (∧ᶜₑ₁ Hir);
            };
            apply ⇒ᶜₑ HirLeft;
            apply Hl++b
          }
        }
      }
      {
        apply ⇒ᶜᵢ;
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
              have tmp: πᶜ (((⟇_to_∨ᶜ_rw l ∨ᶜ ⟇_to_∨ᶜ_rw b) ⇒ᶜ ⟇_to_∨ᶜ_rw (l ++ b))) {
                refine (∧ᶜₑ₂ Hir);
              };
              apply ⇒ᶜₑ tmp;
              apply ∨ᶜᵢ₁;
              apply H2
            }
        } {
          assume H1;
          apply ∨ᶜᵢ₂;
          have tmp: πᶜ (((⟇_to_∨ᶜ_rw l ∨ᶜ ⟇_to_∨ᶜ_rw b) ⇒ᶜ ⟇_to_∨ᶜ_rw (l ++ b))) {
                refine (∧ᶜₑ₂ Hir);
              };
              apply ⇒ᶜₑ tmp;
              apply ∨ᶜᵢ₂;
              apply H1
        }        
      }
    }
end;

constant symbol nnpp_eq p : πᶜ ((¬ ¬ p) = p);

// Axiom propositional_extensionality: forall (P Q : Prop), (P <-> Q) -> P = Q.
// τ o ↪ Prop
constant symbol prop_ext [p: Prop] [q: Prop]: πᶜ (p ⇔ᶜ q) → πᶜ (p = q);

opaque symbol ⟺_ext [p: Prop] [q: Prop]:  πᶜ (p = q) → πᶜ (p ⇔ᶜ q) ≔
begin
  assume p q Heq;  rewrite Heq; apply ⇔ᶜ_refl
end;

opaque symbol iff_equiv_eq p q: πᶜ ((p ⇔ᶜ q) = (p = q)) ≔
begin
  assume p q;
  apply prop_ext;
  apply ∧ᶜᵢ
  { apply ⇒ᶜᵢ; assume Hiff; apply prop_ext Hiff }
  { apply ⇒ᶜᵢ; assume Heq; rewrite Heq; apply ⇔ᶜ_refl }
end;

opaque  symbol ∨ᶜ_assoc_eq x y z : πᶜ ((x ∨ᶜ (y ∨ᶜ z)) = ((x ∨ᶜ y) ∨ᶜ z)) ≔
begin
  assume x y z;
  apply prop_ext;
  apply ∨ᶜ_assoc
end;

opaque  symbol ∧ᶜ_assoc_eq x y z : πᶜ ((x ∧ᶜ (y ∧ᶜ z)) = ((x ∧ᶜ y) ∧ᶜ z)) ≔
begin
  assume x y z;
  apply prop_ext;
  apply ∧ᶜ_assoc
end;

opaque symbol morgan₁ p q : πᶜ ((¬ (p ∧ᶜ q)) = ((¬ p) ∨ᶜ (¬ q))) ≔
begin
  assume p q;
  apply prop_ext;
  apply ∧ᶜᵢ
  {
    apply ⇒ᶜᵢ;
    assume H;
    apply  not_and_or H
  }
  {
    apply ⇒ᶜᵢ;
    assume H;
    refine or_not_and H
  }
end;

opaque symbol morgan₂ p q : πᶜ ((¬ (p ∨ᶜ q)) = ((¬ p) ∧ᶜ (¬ q))) ≔
begin
  assume p q;
  apply prop_ext;
  apply ∧ᶜᵢ
  {
    apply ⇒ᶜᵢ;
    assume H;
    refine not_or_and H
  }
  {
    apply ⇒ᶜᵢ;
    assume H;
    refine and_not_or H
  }
end;

opaque symbol distributive_or p q r : πᶜ ((p ∨ᶜ (q ∧ᶜ r)) = ((p ∨ᶜ q) ∧ᶜ (p ∨ᶜ r))) ≔
begin
  assume p q r;
  apply prop_ext;
  apply ∧ᶜᵢ
  {
    apply ⇒ᶜᵢ;
    assume H;
    apply ∧ᶜᵢ
    {
      apply ∨ᶜₑ H
      { assume Hp; apply ∨ᶜᵢ₁; refine Hp }
      { assume Hqr; apply ∨ᶜᵢ₂; refine ∧ᶜₑ₁ Hqr }
    }
    {
      apply ∨ᶜₑ H
      { assume Hp; apply ∨ᶜᵢ₁; refine Hp }
      { assume Hqr; apply ∨ᶜᵢ₂; refine ∧ᶜₑ₂ Hqr }
    }
  }
  {
    apply ⇒ᶜᵢ;
    assume H;
    have H1: πᶜ (p ∨ᶜ q) { apply ∧ᶜₑ₁ H  };
    have H2: πᶜ (p ∨ᶜ r) { apply ∧ᶜₑ₂ H  };
    apply ∨ᶜₑ H1
    { 
        assume Hp;
        apply ∨ᶜₑ H2
        {
          assume Hp';
          apply ∨ᶜᵢ₁;
          apply Hp';
        }
        {
          assume Hr;
          apply ∨ᶜᵢ₁;
          apply Hp;
        }  
    }
    {
      assume Hq;
      apply ∨ᶜₑ H2
        {
          assume Hp';
          apply ∨ᶜᵢ₁;
          apply Hp';
        }
        {
          assume Hr;
          apply ∨ᶜᵢ₂;
          apply ∧ᶜᵢ
          { refine Hq }
          { refine Hr }
        }  
    };
  }
end;

opaque symbol distributive_and p q r : πᶜ ((p ∧ᶜ (q ∨ᶜ r)) = ((p ∧ᶜ q) ∨ᶜ (p ∧ᶜ r))) ≔
begin
  assume p q r;
  apply prop_ext;
  apply ∧ᶜᵢ
  {
    apply ⇒ᶜᵢ;
    assume H;
    have Hp: πᶜ p { apply ∧ᶜₑ₁ H };
    have Hqorr: πᶜ (q ∨ᶜ r) { apply ∧ᶜₑ₂ H };
    apply ∨ᶜₑ Hqorr
    { 
      assume Hq;
      apply ∨ᶜᵢ₁;
      apply ∧ᶜᵢ { refine Hp } { refine Hq }
    }
    {
      assume Hr;
      apply ∨ᶜᵢ₂;
      apply ∧ᶜᵢ { refine Hp } { refine Hr  }
    }
  }
  {
    apply ⇒ᶜᵢ;
    assume H;
    apply ∨ᶜₑ H
    {
      assume Hpandq;
      apply ∧ᶜᵢ { refine ∧ᶜₑ₁ Hpandq  } { apply ∨ᶜᵢ₁; refine ∧ᶜₑ₂ Hpandq }
    }
    {
      assume Hpandr;
      apply ∧ᶜᵢ { refine ∧ᶜₑ₁ Hpandr  } { apply ∨ᶜᵢ₂; refine ∧ᶜₑ₂ Hpandr }
    }
  }
end;

opaque symbol and_com p q : πᶜ ((p ∧ᶜ q) = (q ∧ᶜ p)) ≔
begin
  assume p q;
  apply prop_ext;
  apply ∧ᶜᵢ
  { apply ⇒ᶜᵢ; assume Hpq; apply ∧ᶜ_com Hpq }
  { apply ⇒ᶜᵢ; assume Hqp; apply ∧ᶜ_com Hqp }
end;

opaque symbol or_com p q : πᶜ ((p ∨ᶜ q) = (q ∨ᶜ p)) ≔
begin
  assume p q;
  apply prop_ext;
  apply ∧ᶜᵢ
  { apply ⇒ᶜᵢ; assume Hpq; apply ∨ᶜ_com Hpq }
  { apply ⇒ᶜᵢ; assume Hpq; apply ∨ᶜ_com Hpq }
end;

opaque symbol or_idempotent p : πᶜ ((p ∨ᶜ p) = p) ≔
begin
  assume p;
  apply prop_ext;
  apply ∧ᶜᵢ
  {
    apply ⇒ᶜᵢ;
    assume Hporp;
    apply ∨ᶜₑ Hporp
    { assume Hp; refine Hp }
    { assume Hp; refine Hp }
  }
  {
    apply ⇒ᶜᵢ;
    assume Hp;
    apply ∨ᶜᵢ₁;
    refine Hp
  }
end;

opaque symbol and_idempotent p : πᶜ ((p ∧ᶜ p) = p) ≔
begin
  assume p;
  apply prop_ext;
  apply ∧ᶜᵢ
  { apply ⇒ᶜᵢ; assume Hpandp; apply ∧ᶜₑ₁ Hpandp; }
  {
    apply ⇒ᶜᵢ;
    assume Hp;
    apply ∧ᶜᵢ { refine Hp } { refine Hp }
  }
end;

opaque symbol imp_eq_or p q: πᶜ (((¬ p) ∨ᶜ q) =  (p ⇒ᶜ q)) ≔
begin
  assume p q;
  apply prop_ext;
  apply ∧ᶜᵢ
  { apply ⇒ᶜᵢ; assume Hor; apply or_to_imply Hor }
  { apply ⇒ᶜᵢ; assume Himp; apply imply_to_or Himp }
end;

opaque symbol contrapos [p q] : πᶜ (p ⇒ᶜ q  ⇔ᶜ (¬ q ⇒ᶜ ¬ p)) ≔
begin
  assume p q;
  apply ∧ᶜᵢ
  {
    apply ⇒ᶜᵢ;
    assume Himp;
    apply ⇒ᶜᵢ;
    assume Hnq;
    apply ¬ᶜᵢ;
    assume Hp;
    have Hq: πᶜ q
    {  apply ⇒ᶜₑ Himp Hp };
    apply ¬ᶜₑ Hnq Hq
  }
  {
    apply ⇒ᶜᵢ;
    assume Himp;
    apply ⇒ᶜᵢ;
    assume Hp;
    have Hor: πᶜ ((¬ ¬ q) ∨ᶜ ¬ p) {
      rewrite imp_eq_or;
      apply Himp
    };
    apply ∨ᶜₑ Hor
    { assume Hnnq; rewrite left  nnpp_eq; apply Hnnq }
    { assume Hnp; apply  ¬ᶜₑ Hnp Hp }
  };
end;

opaque symbol contradiction p : (πᶜ (¬ p) → πᶜ ⊥) → πᶜ p ≔
begin
  assume p Hnp;
  admit
end;

// // Hilbert epsilon operator/choice
symbol ϵ  [a]: (τ a → Prop) → τ a; notation ϵ quantifier;

constant symbol ϵᵢ [a] x (p: τ a → Prop) : πᶜ (p x) → πᶜ (p (ϵ p));
constant symbol ϵ_det [a p q]: Π (x: τ a), πᶜ ((p x) ⇔ᶜ (q x)) → πᶜ (ϵ p = ϵ q);

opaque symbol ϵ_to_∃ [a] p: πᶜ ((`∃ᶜ (x : τ a),  p x) = p (`ϵ (x : τ a), p x)) ≔
begin
  assume a p;
  apply prop_ext;
  apply ∧ᶜᵢ
  {
    apply ⇒ᶜᵢ;
    assume H;
    apply ∃ᶜₑ _ H;
    assume x H1;
    apply ϵᵢ x (λ u, (p u)) H1;
  }
  {
    apply ⇒ᶜₑ (∧ᶜₑ₂ (@contrapos (p (`ϵ x, p x) ) (`∃ᶜ x, p x)));
    apply ⇒ᶜᵢ;
    assume H;
    have H1: πᶜ (`∀ᶜ x, ¬ p x) { apply (⇒ᶜₑ (∧ᶜₑ₁ (nex_forall p)) H) };
    admit
    //type ∀ᶜₑ (λ u, ¬ (p u)) H1
  }
end;

opaque symbol ϵ_to_∀ [a] p: πᶜ ((`∀ᶜ (x : τ a), p x) = p (`ϵ (x : τ a), (¬ p x))) ≔
begin
  assume a p;
  apply prop_ext;
  apply ∧ᶜᵢ
  {
    apply ⇒ᶜᵢ;
    assume H;
    apply ∀ᶜₑ (`ϵ x, ¬ (p x)) H
  }
  {
    apply ⇒ᶜₑ (∧ᶜₑ₂ (@contrapos (p (`ϵ x, ¬ (p x)) ) (`∀ᶜ x, p x)));
    apply ⇒ᶜᵢ;
    assume H;
    have H1: πᶜ (`∃ᶜ x, ¬ p x) { refine (⇒ᶜₑ (∧ᶜₑ₁ (nforall_ex p)) H) };
    apply ∃ᶜₑ _ H1;
    assume x Hnpx;
    apply ϵᵢ x (λ u, ¬ (p u)) Hnpx;
  }
end;

opaque  symbol and_identity_r x : πᶜ ((x ∧ᶜ ⊤) = x) ≔
begin
  assume x;
  apply prop_ext;
  apply ∧ᶜᵢ
  { apply ⇒ᶜᵢ; assume Hand; apply ∧ᶜₑ₁ Hand  }
  { apply ⇒ᶜᵢ; assume Hx; apply ∧ᶜᵢ { refine Hx } { refine trivial } }
end;

opaque  symbol and_identity_l x : πᶜ ((⊤ ∧ᶜ x) = x) ≔
begin
  assume x;
  apply prop_ext;
  apply ∧ᶜᵢ
  { apply ⇒ᶜᵢ; assume Hand; apply ∧ᶜₑ₂ Hand  }
  { apply ⇒ᶜᵢ; assume Hx; apply ∧ᶜᵢ { refine trivial } { refine Hx } }
end;

opaque  symbol and_domination x : πᶜ ((x ∧ᶜ ⊥) = ⊥) ≔
begin
  assume x;
  apply prop_ext;
  apply ∧ᶜᵢ
  { apply ⇒ᶜᵢ; assume Hand; apply ∧ᶜₑ₂ Hand  }
  { apply ⇒ᶜᵢ; assume Hx; apply ⊥ᶜₑ Hx }
end;

opaque  symbol or_identity_l x : πᶜ ((⊥ ∨ᶜ x) = x) ≔
begin
  assume x;
  apply prop_ext;
  apply ∧ᶜᵢ
  { apply ⇒ᶜᵢ; assume Hor; apply ∨ᶜₑ Hor { assume Hbot; apply ⊥ᶜₑ; refine Hbot } { assume Hx; refine Hx }  }
  { apply ⇒ᶜᵢ; assume Hx; apply ∨ᶜᵢ₂; refine Hx }
end;

opaque  symbol or_identity_r x : πᶜ ((x ∨ᶜ ⊥) = x) ≔
begin
  assume x;
  apply prop_ext;
  apply ∧ᶜᵢ
  { apply ⇒ᶜᵢ; assume Hor; apply ∨ᶜₑ Hor { assume Hx; refine Hx } { assume Hbot; apply ⊥ᶜₑ; refine Hbot } }
  { apply ⇒ᶜᵢ; assume Hx; apply ∨ᶜᵢ₁; refine Hx }
end;

opaque symbol ϵ_equiv_∃ᶜ' [a p] : πᶜ ((`∃ᶜ (x: τ a), p x) = (p (`ϵ x, p x))) ≔
begin
  assume a p;
  apply prop_ext;
  apply ∧ᶜᵢ
  {
    apply ⇒ᶜᵢ;
    assume Hexist;
    apply ∃ᶜₑ _ Hexist;
    assume x Hpx;
    apply ϵᵢ x (λ u, p u);
    apply Hpx
  }
  {
    apply ⇒ᶜᵢ;
    assume Heps;
    apply ∃ᶜᵢ _ (`ϵ x, p x);
    apply Heps
  } 
end;

opaque symbol ϵ_equiv_∃ᶜ [a p] : πᶜ ((`∃ᶜ x: τ a, p x) ⇔ᶜ (p (`ϵ x, p x))) ≔
begin
  assume a p;
  apply ∧ᶜᵢ
  {
    apply ⇒ᶜᵢ;
    assume Hexist;
    apply ∃ᶜₑ _ Hexist;
    assume x Hpx;
    apply ϵᵢ x (λ u, p u);
    apply Hpx
  }
  {
    apply ⇒ᶜᵢ;
    assume Heps;
    apply ∃ᶜᵢ _ (`ϵ x, p x);
    apply Heps
  } 
end;

symbol ite [a] (c: τ o) (t e: τ a): τ a;

constant symbol iteI [a] : Π (c: τ o) (t e: τ a) p,
  (πᶜ c → πᶜ (p t))
  → ((πᶜ c → πᶜ ⊥) → πᶜ (p e))
  → πᶜ (p (ite c t e));
// symbol ite (c t e: τ o) ≔ (c ⇒ᶜ t) ∧ᶜ ((¬ c) ⇒ᶜ e);
// constant symbol iteI : Π c t e p,
//                            (πᶜ c → πᶜ (p t))
//                          → ((πᶜ c → πᶜ ⊥) → πᶜ (p e))
//                          → πᶜ (p (ite c t e));                         

opaque symbol ∨ᶜ_to_⟇ a b: πᶜ (a ∨ᶜ b) → π̇ (a ⟇ b ⟇ ▩) ≔
begin
  assume a b Haorb;
  apply ∨ᶜₑ Haorb
  { assume Ha;  apply ∨ᶜᵢ₁; apply Ha }
  {  assume Hb; apply ∨ᶜᵢ₂; apply ∨ᶜᵢ₁; apply Hb }
end;

opaque symbol cong [a b] (f:τ a → τ b) [x x':τ a] : πᶜ(x = x') → πᶜ(f x = f x') ≔
begin
  assume a b f x x' xx'; rewrite xx'; reflexivity;
end;

opaque symbol cong2 [a b c] (f:τ a → τ b → τ c):
  Π [x x':τ a], πᶜ (x = x') → Π [y y':τ b], πᶜ (y = y') → πᶜ (f x y = f x' y') ≔
begin
  assume a b c f x x' xx' y y' yy'; rewrite xx'; rewrite yy'; reflexivity
end;


opaque symbol cong3 [a b c d] (f:τ a → τ b → τ c → τ d):
  Π [x x':τ a], πᶜ (x = x') → Π [y y':τ b], πᶜ (y = y') → Π [z z':τ c], πᶜ (z = z') → πᶜ (f x y z = f x' y' z') ≔
begin
  assume a b c d f x x' xx' y y' yy' z z' zz'; rewrite xx'; rewrite yy'; rewrite zz'; reflexivity
end;

opaque symbol ite1' [c t e] : πᶜ (ite c t e ⇒ᶜ c ∨ᶜ e) ≔
begin
  assume c t e;
  apply iteI c t e (λ u, u ⇒ᶜ (c ∨ᶜ e)) 
  {
    assume Hc;
    apply ⇒ᶜᵢ;
    assume Ht;
    apply ∨ᶜᵢ₁;
    apply Hc
  }
  {
    assume Hnc;
    apply ⇒ᶜᵢ;
    assume He;
    apply ∨ᶜᵢ₂;
    apply He
  }
end;

opaque symbol ite1 (c t e: τ o) : πᶜ (ite c t e) → π̇ (c ⟇ e ⟇ ▩) ≔
begin
  assume c t e H;
  simplify;
  rewrite or_identity_r;
  apply (⇒ᶜₑ (@ite1' c t e)) H;
end;

opaque symbol ite2' [c t e] : πᶜ (ite c t e ⇒ᶜ ((¬ c) ∨ᶜ t)) ≔
begin
  assume c t e;
  apply iteI c t e (λ u, u ⇒ᶜ (¬ c ∨ᶜ t)) 
  {
    assume Hc;
    apply ⇒ᶜᵢ;
    assume Ht;
    apply ∨ᶜᵢ₂;
    apply Ht
  }
  {
    assume Hc;
    apply ⇒ᶜᵢ;
    assume He;
    remove He;
    apply ∨ᶜᵢ₁;
    simplify;
    apply ⇒ᶜᵢ';
    refine Hc
  };
end;

opaque symbol ite2 (c t e: τ o) : πᶜ (ite c t e) → π̇ ((¬ c) ⟇ t ⟇ ▩) ≔
begin
  assume c t e H;
  simplify;
  rewrite or_identity_r;
  apply (⇒ᶜₑ (@ite2' c t e)) H;
end;

// Use it to unfold the definition of `¬`.
// The tactic simplify is to agressive.
opaque symbol negdef p : πᶜ ((p ⇒ ⊥) = ¬ p) ≔
begin
  simplify; reflexivity
end;

opaque symbol ite_pos1 [c t e] : π̇ ((¬ (ite c t e)) ⟇ c ⟇ e ⟇ ▩) ≔
begin
  assume c t e;
  apply imply_to_or;
  apply ⇒ᶜᵢ;
  assume H;
  simplify;
  rewrite or_identity_r;
  apply (⇒ᶜₑ (@ite1' c t e)) H;
end;

opaque symbol ite_pos2 [c t e] : π̇ (¬ (ite c t e) ⟇ ¬ c ⟇ t ⟇ ▩) ≔
begin
  assume c t e;
  apply imply_to_or;
  apply ⇒ᶜᵢ;
  assume H;
  simplify;
  rewrite or_identity_r;
  apply (⇒ᶜₑ (@ite2' c t e)) H;
end;

opaque symbol ite_neg1 [c t e] : π̇ ((ite c t e) ⟇ c ⟇ ¬ e ⟇ ▩) ≔
begin
  assume c t e;
  simplify;
  rewrite or_identity_r;
  apply iteI c t e (λ u, u ∨ᶜ (c ∨ᶜ (e ⇒ ⊥)))
  {
    assume Hc; apply ∨ᶜᵢ₂; apply ∨ᶜᵢ₁; refine Hc
  }
  {
    assume Hnc; rewrite or_com;
    rewrite left ∨ᶜ_assoc_eq;
    apply ∨ᶜᵢ₂;
    rewrite or_com;
    apply classic;
  };
end;

opaque symbol ite_neg2 [c t e] : π̇ ((ite c t e) ⟇ ¬ c ⟇ ¬ t ⟇ ▩) ≔
begin
  assume c t e;
  simplify;
  rewrite or_identity_r;
  apply iteI c t e (λ u, u ∨ᶜ ((c ⇒ ⊥)∨ᶜ (t ⇒ ⊥)))
  {
    assume Hnc; rewrite or_com;
    rewrite left ∨ᶜ_assoc_eq;
    apply ∨ᶜᵢ₂;
    rewrite or_com;
    apply classic;
  }
  {
    assume Hc; apply ∨ᶜᵢ₂; apply ∨ᶜᵢ₁; apply ⇒ᶜᵢ'; refine Hc
  }
end;

opaque symbol not_ite1' [c t e] : πᶜ (¬ (ite c t e) ⇒ᶜ c ∨ᶜ ¬ e) ≔
begin
  assume c t e;
  apply iteI c t e (λ u, ¬ u ⇒ᶜ c ∨ᶜ ¬ e)
  {
    assume Hc;
    apply ⇒ᶜᵢ;
    assume Hnt;
    apply ∨ᶜᵢ₁;
    refine Hc;
  }
  {
    assume Hcimpbot;
    apply ⇒ᶜᵢ;
    assume Hne;
    apply ∨ᶜᵢ₂;
    apply Hne
  }
end;

opaque symbol not_ite1 [c t e] : πᶜ (¬ (ite c t e)) → π̇( c ⟇ ¬ e ⟇ ▩) ≔
begin
  assume c t e H;
  simplify;
  rewrite or_identity_r;
  apply (⇒ᶜₑ (@not_ite1' c t e) H);
end;

opaque symbol not_ite2' [c t e] : πᶜ (¬ (ite c t e) ⇒ᶜ ¬ c  ∨ᶜ ¬ t) ≔
begin
  assume c t e;
  apply iteI c t e (λ u, ¬ u ⇒ᶜ ¬ c  ∨ᶜ ¬ t)
  { assume Hc; apply ⇒ᶜᵢ; assume Hnt; apply ∨ᶜᵢ₂; refine Hnt }
  { assume Hcimpbot; apply ⇒ᶜᵢ; assume Hne; apply ∨ᶜᵢ₁; simplify; apply ⇒ᶜᵢ'; refine Hcimpbot; }
end;

opaque symbol not_ite2 [c t e] : πᶜ (¬ (ite c t e)) → π̇(¬ c ⟇ ¬ t ⟇ ▩) ≔
begin
  assume c t e H;
  simplify;
  rewrite or_identity_r;
  apply (⇒ᶜₑ (@not_ite2' c t e) H);
end;

opaque symbol ite_cong [a] [c c': τ o] [t t' e e': τ a] : πᶜ (c = c') → πᶜ (t = t') → πᶜ (e = e') → π̇(ite c t e = ite c' t' e' ⟇ ▩) ≔
begin
  assume a c c' t t' e e' Hcc' Htt' Hee';
  simplify;
  rewrite or_identity_r;
  rewrite Hcc';
  rewrite Htt';
  rewrite Hee';
  reflexivity
end;

symbol xor a b ≔ ((¬ a) ∧ᶜ b) ∨ᶜ (a ∧ᶜ (¬ b));

opaque symbol xor_pos1 [a b] : π̇ (¬ (xor a b) ⟇ a ⟇ b ⟇ ▩) ≔
begin
  assume a b;
  simplify;
  apply imply_to_or;
  apply ⇒ᶜᵢ;
  assume H;
  apply ∨ᶜₑ H
  { assume Hnab; apply ∨ᶜᵢ₂;  apply ∨ᶜᵢ₁; apply ∧ᶜₑ₂ Hnab }
  { assume Hnab; apply ∨ᶜᵢ₁; apply ∧ᶜₑ₁ Hnab }
end;

opaque symbol xor_pos2 [a b] : π̇ (¬ (xor a b) ⟇ ¬ a ⟇ ¬ b ⟇ ▩) ≔
begin
  assume a b;
  simplify;
  apply imply_to_or;
  apply ⇒ᶜᵢ;
  assume H;
  apply ∨ᶜₑ H
  { assume Hnab; apply ∨ᶜᵢ₁; apply ∧ᶜₑ₁ Hnab }
  { assume Hnab; apply ∨ᶜᵢ₂;  apply ∨ᶜᵢ₁; apply ∧ᶜₑ₂ Hnab }
end;

opaque symbol xor_neg1 [a b] : π̇ ((xor a b) ⟇ a ⟇ ¬ b ⟇ ▩) ≔
begin
  simplify;
  assume a b;
  rewrite left ∨ᶜ_assoc_eq;
  rewrite or_com;
  rewrite distributive_or;
  apply ∧ᶜᵢ
  {
    rewrite or_identity_r;
    rewrite left ∨ᶜ_assoc_eq;
    apply ∨ᶜᵢ₂;
    rewrite or_com;
    rewrite ∨ᶜ_assoc_eq;
    apply ∨ᶜᵢ₁;
    rewrite or_com;
    apply classic
  }
  {
    rewrite left ∨ᶜ_assoc_eq;
    apply ∨ᶜᵢ₂;
    rewrite left ∨ᶜ_assoc_eq;
    apply ∨ᶜᵢ₂;
    rewrite or_com;
    rewrite ∨ᶜ_assoc_eq;
    apply ∨ᶜᵢ₁;
    apply classic
  }
end;

opaque symbol xor_neg2 [a b] : π̇ ((xor a b) ⟇ ¬ a ⟇ b ⟇ ▩) ≔
begin
  simplify;
  assume a b;
  rewrite left ∨ᶜ_assoc_eq;
  rewrite or_com;
  rewrite distributive_or;
  apply ∧ᶜᵢ
  {
    rewrite left ∨ᶜ_assoc_eq;
    rewrite or_com;
    rewrite distributive_or;
    apply ∧ᶜᵢ
    {
      rewrite left ∨ᶜ_assoc_eq;
      apply ∨ᶜᵢ₂;
      rewrite or_com;
      apply classic
    }
    {
      rewrite or_com;
      rewrite ∨ᶜ_assoc_eq;
      apply ∨ᶜᵢ₁;
      rewrite or_com;
      rewrite left ∨ᶜ_assoc_eq;
      apply ∨ᶜᵢ₂;
      rewrite or_identity_r;
      apply classic
    }
  }
  {
    rewrite left ∨ᶜ_assoc_eq;
    rewrite or_com;
    rewrite distributive_or;
    apply ∧ᶜᵢ
    {
      rewrite or_com;
      rewrite ∨ᶜ_assoc_eq;
      apply ∨ᶜᵢ₁;
      rewrite ∨ᶜ_assoc_eq;
      apply ∨ᶜᵢ₁;
      apply classic
    }
    {
      rewrite or_com;
      rewrite ∨ᶜ_assoc_eq;
      rewrite or_identity_r;
      apply ∨ᶜᵢ₁;
      rewrite or_com;
      rewrite left ∨ᶜ_assoc_eq;
      apply ∨ᶜᵢ₂;
      apply classic
    }
  }
end;

// // i ▷ 𝜑1 ∨ ⋯ ∨ 𝜑n
// // j ▷ 𝜑1 , ⋯ , 𝜑n
constant symbol or [a b] : π̇ ((a ∨ᶜ b) ⟇ ▩) → π̇ (∨ᶜ_to_⟇_rw  (a ∨ᶜ b));

opaque symbol not_not x : π̇ ( (¬ (¬ (¬ x))) ⟇ x ⟇ ▩) ≔
begin
  assume x;
  apply imply_to_or;
  apply ⇒ᶜᵢ;
  assume H;
  apply ∨ᶜᵢ₁;
  apply nnpp H
end;

opaque symbol implies [φ₁ φ₂] : πᶜ (φ₁ ⇒ᶜ φ₂) → π̇ (¬ φ₁ ⟇ φ₂ ⟇ ▩) ≔
begin
  assume φ₁ φ₂ Hφ₁⇒ᶜφ₂;
  apply imply_to_or;
  apply ⇒ᶜᵢ;
  assume πφ₁;
  apply ∨ᶜᵢ₁;
  apply ⇒ᶜₑ Hφ₁⇒ᶜφ₂ πφ₁
end;

opaque symbol not_implies1 [φ₁ φ₂] : πᶜ (¬ (φ₁ ⇒ᶜ φ₂)) → π̇ (φ₁ ⟇ ▩) ≔
begin
  assume φ₁ φ₂ Hnot_φ₁⇒ᶜφ₂;
  apply ∨ᶜᵢ₁;
  apply ∧ᶜₑ₁ (imply_to_and Hnot_φ₁⇒ᶜφ₂)
end;

opaque symbol not_implies2 [φ₁ φ₂] : πᶜ (¬ (φ₁ ⇒ᶜ φ₂)) →  π̇ (¬ φ₂ ⟇ ▩) ≔
begin
  assume φ₁ φ₂ Hnot_φ₁⇒ᶜφ₂;
  apply ∨ᶜᵢ₁;
  apply ∧ᶜₑ₂ (imply_to_and Hnot_φ₁⇒ᶜφ₂)
end;

opaque symbol implies_neg1 [φ₁ φ₂] : π̇ (φ₁ ⇒ᶜ φ₂ ⟇ φ₁ ⟇ ▩) ≔
begin
  assume φ₁ φ₂;
  simplify;
  rewrite left imp_eq_or;
  rewrite ∨ᶜ_assoc_eq;
  apply ∨ᶜᵢ₁;
  rewrite .[(¬ φ₁) ∨ᶜ φ₂] or_com;
  rewrite left ∨ᶜ_assoc_eq;
  apply ∨ᶜᵢ₂;
  rewrite or_com;
  apply classic
end;

opaque symbol implies_neg2 [φ₁ φ₂] : π̇ (φ₁ ⇒ᶜ φ₂ ⟇ ¬ φ₂ ⟇ ▩) ≔
begin
  assume φ₁ φ₂;
  simplify;
  rewrite left imp_eq_or;
  rewrite ∨ᶜ_assoc_eq;
  apply ∨ᶜᵢ₁;
  rewrite left ∨ᶜ_assoc_eq;
  apply ∨ᶜᵢ₂;
  apply classic
end;

opaque symbol equiv1 [φ₁ φ₂] : π̇ (φ₁ = φ₂ ⟇ ▩) → π̇ ((¬ φ₁) ⟇ φ₂ ⟇ ▩) ≔
begin
  assume φ₁ φ₂ H1;
  apply ∨ᶜₑ H1
  {
    assume Hequiv;
    have Hequiv':  πᶜ (φ₁ ⇔ᶜ φ₂) { apply ⟺_ext; apply Hequiv };
    have H2: πᶜ (φ₁ ⇒ᶜ φ₂) { apply ∧ᶜₑ₁ Hequiv' };
    have H3: πᶜ (φ₂ ⇒ᶜ φ₁) { apply ∧ᶜₑ₂ Hequiv' };
    have Hassoc: πᶜ (((¬ φ₁) ∨ᶜ (φ₂ ∨ᶜ ⊥)) ⇔ᶜ  (((¬ φ₁) ∨ᶜ φ₂) ∨ᶜ ⊥)) {
      apply (@∨ᶜ_assoc (¬ φ₁) φ₂ ⊥);
    };
    have Hassoc_left: πᶜ ((((¬ φ₁) ∨ᶜ φ₂) ∨ᶜ ⊥)  ⇒ᶜ  ((¬ φ₁) ∨ᶜ (φ₂ ∨ᶜ ⊥))) {
      refine ∧ᶜₑ₂ Hassoc
    };
    apply ⇒ᶜₑ Hassoc_left;
    apply ∨ᶜᵢ₁;
    apply imply_to_or;
    refine H2;
  }
  {
    assume Hbot;
    apply ∨ᶜᵢ₂;
    apply ∨ᶜᵢ₂;
    apply Hbot;
  }
end;

opaque symbol equiv2 [φ₁ φ₂] : π̇ (φ₁ = φ₂ ⟇ ▩)  → π̇ (φ₁ ⟇ (¬ φ₂) ⟇ ▩) ≔
begin
  assume φ₁ φ₂ H1;
  apply ∨ᶜₑ H1
  {
    assume Hequiv;
    have Hequiv':  πᶜ (φ₁ ⇔ᶜ φ₂) { apply ⟺_ext; apply Hequiv };
    have H2: πᶜ (φ₁ ⇒ᶜ φ₂) { apply ∧ᶜₑ₁ Hequiv' };
    have H3: πᶜ (φ₂ ⇒ᶜ φ₁) { apply ∧ᶜₑ₂ Hequiv' };
    have Hassoc: πᶜ ((φ₁ ∨ᶜ ((¬ φ₂) ∨ᶜ ⊥)) ⇔ᶜ  ((φ₁ ∨ᶜ (¬ φ₂)) ∨ᶜ ⊥)) {
      apply (@∨ᶜ_assoc φ₁ (¬ φ₂) ⊥);
    };
    have Hassoc_left: πᶜ (((φ₁ ∨ᶜ (¬ φ₂)) ∨ᶜ ⊥)  ⇒ᶜ  (φ₁ ∨ᶜ ((¬ φ₂) ∨ᶜ ⊥))) {
      refine ∧ᶜₑ₂ Hassoc
    };
    apply ⇒ᶜₑ Hassoc_left;
    apply ∨ᶜᵢ₁;
    apply ∨ᶜ_com;
    apply imply_to_or;
    refine H3;
  }
  {
    assume Hbot;
    apply ∨ᶜᵢ₂;
    apply ∨ᶜᵢ₂;
    apply Hbot;
  }
end;

opaque symbol equiv_pos1 [φ₁ φ₂] : π̇ ((¬ (φ₁ = φ₂)) ⟇ φ₁ ⟇ ¬ φ₂ ⟇ ▩) ≔
begin
  simplify;
  assume p q;
  apply imply_to_or;
  apply ⇒ᶜᵢ;
  assume Heq;
  rewrite Heq;
  rewrite ∨ᶜ_assoc_eq;
  apply ∨ᶜᵢ₁;
  apply classic
end;

opaque symbol equiv_pos2 [φ₁ φ₂] : π̇ ((¬ (φ₁ = φ₂)) ⟇ (¬ φ₁) ⟇ φ₂ ⟇ ▩) ≔
begin
  simplify;
  assume p q;
  apply imply_to_or;
  apply ⇒ᶜᵢ;
  assume Heq;
  rewrite or_identity_r;
  apply ∨ᶜ_com;
  rewrite Heq;
  apply classic
end;

opaque symbol equiv_neg1 [φ₁ φ₂] : π̇ ((φ₁ = φ₂) ⟇ ¬ φ₁ ⟇ ¬ φ₂ ⟇ ▩) ≔
begin
  simplify;
  assume p q;
  rewrite or_identity_r;
  apply ∨ᶜ_com;
  rewrite left ∨ᶜ_assoc_eq;
  apply imply_to_or;
  apply ⇒ᶜᵢ;
  assume Hp;
  apply imply_to_or;
  apply ⇒ᶜᵢ;
  assume Hq;
  apply prop_ext;
  apply ∧ᶜᵢ
  { apply ⇒ᶜᵢ; assume Hp'; apply Hq }
  { apply ⇒ᶜᵢ; assume Hq'; apply Hp }
end;

opaque symbol equiv_neg2 [φ₁ φ₂] : π̇ ((φ₁ = φ₂) ⟇ φ₁ ⟇ φ₂ ⟇ ▩) ≔
begin
  simplify;
  assume p q;
  rewrite or_identity_r;
  rewrite left iff_equiv_eq;
  apply ∨ᶜ_com;
  simplify;
  rewrite distributive_or; //(p ∨ᶜ q) (p ⇒ᶜ q) (q ⇒ᶜ p);
  apply ∧ᶜᵢ
  {
    rewrite left imp_eq_or;
    rewrite left ∨ᶜ_assoc_eq;
    rewrite .[(¬ p) ∨ᶜ q] or_com;
    rewrite  .[q ∨ᶜ (q ∨ᶜ ¬ p)] ∨ᶜ_assoc_eq;
    rewrite or_idempotent;
    rewrite .[q ∨ᶜ (¬ p)] or_com;
    rewrite ∨ᶜ_assoc_eq;
    apply ∨ᶜᵢ₁;
    apply classic
  }
  {
    rewrite left imp_eq_or;
    rewrite ∨ᶜ_assoc_eq;
    rewrite .[p ∨ᶜ q] or_com;
    rewrite left .[((q ∨ᶜ p) ∨ᶜ ¬ q)] ∨ᶜ_assoc_eq;
    apply ∨ᶜᵢ₁;
    rewrite .[p ∨ᶜ ¬ q] or_com;
    rewrite ∨ᶜ_assoc_eq;
    apply ∨ᶜᵢ₁;
    apply classic
  }
end;

opaque symbol implies_pos [φ₁ φ₂] : π̇ ((¬ (φ₁ ⇒ᶜ φ₂)) ⟇ ¬ φ₁ ⟇ φ₂ ⟇ ▩) ≔
begin
  simplify;
  assume x y;
  rewrite or_identity_r;
  rewrite left imp_eq_or;
  apply ∨ᶜ_com;
  apply classic
end;

opaque symbol not_symm [a] [x y: τ a] : πᶜ (¬ (x = y)) → πᶜ (¬ (y = x)) ≔
begin
  simplify;
  assume a x y H;
  admit
end;

symbol trans [U] [a b c: τ U]: π̇ (a = b ⟇ ▩) → π̇ (b = c ⟇ ▩) → π̇ (a = c ⟇ ▩) ≔
begin
  assume U a b c H1 H2;
  apply ∨ᶜᵢ₁;
  have H2': πᶜ (b = c) { apply π̇ₗ H2 };
  have H1': πᶜ (a = b) { apply π̇ₗ H1 };
  rewrite H1';
  apply H2'
end;

opaque symbol subproof1 [φ₁ ψ] : πᶜ φ₁ → πᶜ ψ → π̇ ((¬ φ₁) ⟇ ψ ⟇ ▩) ≔
begin
  assume φ₁ ψ Hφ₁ Hψ;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₁;
  apply Hψ
end;

opaque symbol subproof2 [φ₁ φ₂ ψ] : πᶜ φ₁ → πᶜ φ₂ → πᶜ ψ → π̇ ((¬ φ₁) ⟇ (¬ φ₂) ⟇ ψ ⟇ ▩) ≔
begin
  assume φ₁ φ₂ ψ Hφ₁ Hφ₂ Hψ;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₁;
  apply Hψ;
end;

opaque symbol subproof3 [φ₁ φ₂ φ₃ ψ] : πᶜ φ₁ → πᶜ φ₂ → πᶜ φ₃ → πᶜ ψ → π̇ ((¬ φ₁) ⟇ (¬ φ₂) ⟇ (¬ φ₃) ⟇ ψ ⟇ ▩) ≔
begin
  assume φ₁ φ₂ φ₃ ψ Hφ₁ Hφ₂ Hφ₃ Hψ;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₁;
  apply Hψ;
end;

opaque symbol subproof4 [φ₁ φ₂ φ₃ φ₄ ψ] : πᶜ φ₁ → πᶜ φ₂ → πᶜ φ₃ → πᶜ φ₄ → πᶜ ψ → π̇ ((¬ φ₁) ⟇ (¬ φ₂) ⟇ (¬ φ₃) ⟇ (¬ φ₄) ⟇ ψ ⟇ ▩) ≔
begin
  assume φ₁ φ₂ φ₃ φ₄ ψ Hφ₁ Hφ₂ Hφ₃ Hφ₄ Hψ;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₁;
  apply Hψ;
end;

opaque symbol subproof5 [φ₁ φ₂ φ₃ φ₄ φ₅ ψ] : πᶜ φ₁ → πᶜ φ₂ → πᶜ φ₃ → πᶜ φ₄ → πᶜ φ₅ → πᶜ ψ → π̇ ((¬ φ₁) ⟇ (¬ φ₂) ⟇ (¬ φ₃) ⟇ (¬ φ₄) ⟇ (¬ φ₅) ⟇ ψ ⟇ ▩) ≔
begin
  assume φ₁ φ₂ φ₃ φ₄ φ₅ ψ Hφ₁ Hφ₂ Hφ₃ Hφ₄ Hφ₅ Hψ;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₁;
  apply Hψ;
end;

opaque symbol subproof6 [φ₁ φ₂ φ₃ φ₄ φ₅ φ₆ ψ] : πᶜ φ₁ → πᶜ φ₂ → πᶜ φ₃ → πᶜ φ₄ → πᶜ φ₅ → πᶜ φ₆ → πᶜ ψ → π̇ ((¬ φ₁) ⟇ (¬ φ₂) ⟇ (¬ φ₃) ⟇ (¬ φ₄) ⟇ (¬ φ₅) ⟇ (¬ φ₆) ⟇ ψ ⟇ ▩) ≔
begin
  assume φ₁ φ₂ φ₃ φ₄ φ₅ φ₆ ψ Hφ₁ Hφ₂ Hφ₃ Hφ₄ Hφ₅ Hφ₆ Hψ;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₂;
  apply ∨ᶜᵢ₁;
  apply Hψ;
end;

opaque symbol forall_inst1 [a] p (x: τ a) : πᶜ (¬ (`∀ᶜ x', p x') ∨ᶜ (p x)) ≔
begin
 assume a p x;
 rewrite imp_eq_or;
 apply ⇒ᶜᵢ;
 assume H;
 apply ∀ᶜₑ x H
end;

opaque symbol forall_inst2 [a] p (x y: τ a) : πᶜ (¬ (`∀ᶜ a, `∀ᶜ b, p a b) ∨ᶜ (p x y)) ≔
begin
  assume a p x y;
  rewrite imp_eq_or;
  apply ⇒ᶜᵢ;
  assume H;
  apply ∀ᶜₑ y (∀ᶜₑ x H)
 end;

opaque symbol forall_inst3 [a] [p] (x y z: τ a) : πᶜ ((¬ (`∀ᶜ a, `∀ᶜ b, `∀ᶜ c, p a b c)) ∨ᶜ ((p x y z) ∨ᶜ ⊥)) ≔
begin
  assume a p x y z;
  apply imply_to_or;
  apply ⇒ᶜᵢ;
  assume H;
  apply ∨ᶜᵢ₁ (∀ᶜₑ z (∀ᶜₑ y (∀ᶜₑ x H)))
end;

// # In Predicate
// 
// The In predicate works with 𝔹 instead of Prop to avoid making critical pairs wiht other rules.
// If we use Prop, then we will need a rule
// ▷ `$x ⇔ᶜ $x ↪ ⊤` to replace `eq $x $h` and, 
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

// Decidable equality in 𝔹.
// Symbol = has been declared constant, it cannot be used as the head of a rewrite rule LHS.
// So we create our own eq symbol.

// symbol 𝑰 [a]: ℕ → τ a; 

sequential symbol eq : Prop → Prop → 𝔹;
rule eq $x $x ↪ true
with eq $x $y ↪ false;

sequential symbol In_∧ᶜ: Prop → Prop → 𝔹;
rule In_∧ᶜ $x ($h ∧ᶜ $tl) ↪ (eq $x $h)  Stdlib.Bool.or (In_∧ᶜ $x $tl)
with In_∧ᶜ $x ⊤ ↪ false;

sequential symbol In_∨ᶜ: Prop → Prop → 𝔹;
rule In_∨ᶜ $x ($h ∨ᶜ $tl) ↪ (eq $x $h) Stdlib.Bool.or (In_∨ᶜ $x $tl)
with In_∨ᶜ _ ⊥ ↪ false;

sequential symbol In_∧ᶜ': Prop → Prop → 𝔹;
rule In_∧ᶜ' $x ($h ∧ᶜ $tl) ↪ (eq $x $h)  Stdlib.Bool.or (In_∧ᶜ' $x $tl)
with In_∧ᶜ' $x $h ↪ (eq $x $h);

sequential symbol In_∨ᶜ': Prop → Prop → 𝔹;
rule In_∨ᶜ' $x ($h ∨ᶜ $tl) ↪ (eq $x $h) Stdlib.Bool.or (In_∨ᶜ' $x $tl)
with In_∨ᶜ' $x $h ↪ (eq $x $h);

// and_pos: ¬(𝜑1 ∧ … ∧ 𝜑𝑛), 𝜑𝑘
symbol and_pos [φ₁__φₙ φₖ]:  πᶜ ((In_∧ᶜ' φₖ φ₁__φₙ) = true) → π̇ (¬ φ₁__φₙ ⟇ φₖ ⟇ ▩);

opaque symbol test_and_pos: π̇ ((¬ (a ∧ᶜ b ∧ᶜ c ∧ᶜ d)) ⟇ d ⟇ ▩) ≔
begin
  apply and_pos;
  reflexivity;
end; 

// and_neg:  (𝜑1 ∧ ⋯ ∧ 𝜑𝑛), ¬𝜑1, … , ¬𝜑𝑛
sequential symbol and_neg_r: Prop → Clause → 𝔹; 
rule and_neg_r ($x ∧ᶜ $tl) (($x ⇒ ⊥) ⟇ $tl2) ↪ and_neg_r $tl $tl2
with and_neg_r ⊤ ▩ ↪ true; 

sequential symbol and_neg_r': Prop → Clause → 𝔹; 
rule and_neg_r' ($x ∧ᶜ $tl) (($x ⇒ ⊥) ⟇ $tl2) ↪ and_neg_r' $tl $tl2
with and_neg_r' ($x) (($x ⇒ ⊥) ⟇ ▩) ↪ true;
//with and_neg_r ⊤ ▩ ↪ true; 

symbol and_neg [l1 l2]: πᶜ (and_neg_r' l1 l2 = true) → π̇ (l1 ⟇ l2);

opaque symbol test_and_neg: π̇ ((a ∧ᶜ b ∧ᶜ c ∧ᶜ d) ⟇ (¬ a) ⟇ (¬ b) ⟇ (¬ c) ⟇ (¬ d) ⟇ ▩) ≔
begin
  apply and_neg;
  reflexivity;
end; 

// or_pos:  ¬(𝜑1 ∨ ⋯ ∨ 𝜑𝑛), 𝜑1 , … , 𝜑𝑛
sequential symbol or_pos_r: Prop → Clause → 𝔹; 
rule or_pos_r ($x ∨ᶜ $tl) ($x ⟇ $tl2) ↪ or_pos_r $tl $tl2
with or_pos_r ⊥ ▩ ↪ true; 

sequential symbol or_pos_r': Prop → Clause → 𝔹; 
rule or_pos_r' ($x ∨ᶜ $tl) ($x ⟇ $tl2) ↪ or_pos_r' $tl $tl2
with or_pos_r' $x ($x ⟇ ▩) ↪ true;

symbol or_pos [l1 l2]: πᶜ (or_pos_r' l1 l2 = true) → π̇ (¬ l1 ⟇ l2);

opaque symbol test_or_pos: π̇ (¬ (a ∨ᶜ b ∨ᶜ c ∨ᶜ d) ⟇ a ⟇ b ⟇ c ⟇ d ⟇ ▩) ≔
begin
  apply or_pos; reflexivity
end; 

// or_neg:
// i. ▷ (𝜑1 ∨ ⋯ ∨ 𝜑𝑛), ¬𝜑k
symbol or_neg [φ₁__φₙ] φₖ:  πᶜ ((In_∨ᶜ' φₖ φ₁__φₙ) = true) → π̇ (φ₁__φₙ ⟇ ¬ φₖ ⟇ ▩);

opaque symbol test_or_neg: π̇ (((a ∨ᶜ b ∨ᶜ c ∨ᶜ d)) ⟇ ¬ c ⟇ ▩) ≔
begin
  apply or_neg; reflexivity
end; 

// not_or:
// i. ▷ ¬(𝜑1 ∨ ⋯ ∨ 𝜑𝑛)
// j. ▷ ¬𝜑𝑘
symbol not_or [φₖ] φ₁__φₙ: πᶜ (¬ φ₁__φₙ) → πᶜ ((In_∨ᶜ' φₖ φ₁__φₙ) = true) → π̇ (¬ φₖ ⟇ ▩);

opaque symbol identity_⊥ [x] : πᶜ (x ∨ᶜ ⊥) → πᶜ x ≔
begin
  assume x H;
  apply ∨ᶜₑ H
  { assume Hx; apply Hx } { assume H⊥; apply ⊥ᶜₑ; apply H⊥ }
end;

opaque symbol test_not_or: π̇ (¬ (a ∨ᶜ b ∨ᶜ c ∨ᶜ d) ⟇ ▩) → π̇ (¬ c ⟇ ▩) ≔
begin
  assume H; // i
  apply not_or (a ∨ᶜ b ∨ᶜ c ∨ᶜ d)
    { apply π̇ₗ; apply H }
    { reflexivity }
end;

// not_and:
// i. ▷ ¬(𝜑1 ∧ … ∧ 𝜑𝑛)
// j. ▷ ¬𝜑1, … , ¬𝜑𝑛
sequential symbol not_and_r: Prop → Clause → 𝔹; 
rule not_and_r ($x ∧ᶜ $tl) (($x ⇒ ⊥) ⟇ $tl2) ↪ not_and_r $tl $tl2
with not_and_r ⊤ ▩ ↪ true; 

sequential symbol not_and_r': Prop → Clause → 𝔹; 
rule not_and_r' ($x ∧ᶜ $tl) (($x ⇒ ⊥) ⟇ $tl2) ↪ not_and_r' $tl $tl2
with not_and_r' $x (($x ⇒ ⊥) ⟇ ▩) ↪ true;

symbol not_and [l1 l2]: πᶜ (¬ l1) → πᶜ (not_and_r' l1 l2 = true) → π̇ l2;

opaque symbol test_not_and: π̇ (¬ (a ∧ᶜ b ∧ᶜ c ∧ᶜ d) ⟇ ▩) → π̇ (¬ a ⟇ ¬ b ⟇ ¬ c ⟇ ¬ d ⟇ ▩) ≔
begin
  assume t1;
  apply not_and (π̇ₗ t1);
  reflexivity
end; 

// and:
// i. ▷ (𝜑1 ∧ ⋯ ∧ 𝜑𝑛)
// j. ▷ 𝜑𝑘
symbol and [φₖ] φ₁__φₙ : πᶜ ((In_∧ᶜ' φₖ φ₁__φₙ) = true) → π̇ (φ₁__φₙ ⟇ ▩)  → π̇ (φₖ ⟇ ▩);

opaque symbol test_and:  π̇ ((a ∧ᶜ b ∧ᶜ c ∧ᶜ d) ⟇ ▩) →  π̇ (c ⟇ ▩) ≔
begin
  assume t1;
  apply and ((a ∧ᶜ b ∧ᶜ (c ∧ᶜ d))) { simplify; reflexivity } { apply t1  };
end;

opaque symbol resolutionₗ x a b: π̇ (x ⟇ a) → π̇ ((¬ x) ⟇ b) → π̇ (a ++ b) ≔ begin
  assume x a b H1 H2;
  apply ⟇ₑ H1 {
    assume Hx;
    apply ⟇ₑ H2 {
      assume Hnx;
      have tmp:  πᶜ ((⟇_to_∨ᶜ_rw a ∨ᶜ ⟇_to_∨ᶜ_rw b)  ⇒ᶜ ⟇_to_∨ᶜ_rw (a ++ b)) {
        apply ∧ᶜₑ₂ (++_to_∨ᶜ a b);
      };
      apply ⇒ᶜₑ tmp; 
      apply ∨ᶜₑ Hx { assume Hpi_x;  apply ∨ᶜₑ Hnx { assume Hpi_nx;  apply ¬ᶜₑ Hpi_nx Hpi_x }  {  assume Hbot; apply ⊥ᶜₑ;  apply Hbot  } } { assume Hbot; apply ⊥ᶜₑ;  apply Hbot  };
    } {
      assume Hb;
      have tmp:  πᶜ ((⟇_to_∨ᶜ_rw a ∨ᶜ ⟇_to_∨ᶜ_rw b)  ⇒ᶜ ⟇_to_∨ᶜ_rw (a ++ b)) {
        apply ∧ᶜₑ₂ (++_to_∨ᶜ a b);
      };
      apply ⇒ᶜₑ tmp;
      apply ∨ᶜᵢ₂;
      apply Hb;
    }
  } {
    assume Ha;
    apply ⟇ₑ H2 {
      assume Hnx;
      have tmp:  πᶜ ((⟇_to_∨ᶜ_rw a ∨ᶜ ⟇_to_∨ᶜ_rw b) ⇒ᶜ ⟇_to_∨ᶜ_rw (a ++ b)) {
        apply ∧ᶜₑ₂ (++_to_∨ᶜ a b);
      };
      apply ⇒ᶜₑ tmp;
      apply ∨ᶜᵢ₁;
      apply Ha
    } {
      assume Hb;
      have tmp:  πᶜ ((⟇_to_∨ᶜ_rw a ∨ᶜ ⟇_to_∨ᶜ_rw b) ⇒ᶜ ⟇_to_∨ᶜ_rw (a ++ b)) {
        apply ∧ᶜₑ₂ (++_to_∨ᶜ a b);
      };
      apply ⇒ᶜₑ  tmp;
      apply ∨ᶜᵢ₁;
      apply Ha
    }
  };
end;

opaque symbol resolutionᵣ x a b: π̇ ((¬ x) ⟇ a) → π̇ (x ⟇ b) → π̇ (a ++ b) ≔ begin
  assume x a b H1 H2;
  apply ⟇ₑ H1 {
    assume Hnx;
    apply ⟇ₑ H2 {
      assume Hx;
      have tmp:  πᶜ ((⟇_to_∨ᶜ_rw a ∨ᶜ ⟇_to_∨ᶜ_rw b) ⇒ᶜ ⟇_to_∨ᶜ_rw (a ++ b)) {
        apply ∧ᶜₑ₂ (++_to_∨ᶜ a b);
      };
      apply ⇒ᶜₑ tmp;
      apply ∨ᶜₑ Hx { assume Hpi_x;  apply ∨ᶜₑ Hnx { assume Hpi_nx;  apply ¬ᶜₑ Hpi_nx Hpi_x }  {  assume Hbot; apply ⊥ᶜₑ;  apply Hbot  } } { assume Hbot; apply ⊥ᶜₑ;  apply Hbot  };
    } {
      assume Hb;
      have tmp:  πᶜ ((⟇_to_∨ᶜ_rw a ∨ᶜ ⟇_to_∨ᶜ_rw b)  ⇒ᶜ ⟇_to_∨ᶜ_rw (a ++ b)) {
        apply ∧ᶜₑ₂ (++_to_∨ᶜ a b);
      };
      apply ⇒ᶜₑ tmp;
      apply ∨ᶜᵢ₂;
      apply Hb;
    }
  } {
    assume Ha;
    apply ⟇ₑ H2 {
      assume Hnx;
      have tmp:  πᶜ ((⟇_to_∨ᶜ_rw a ∨ᶜ ⟇_to_∨ᶜ_rw b) ⇒ᶜ ⟇_to_∨ᶜ_rw (a ++ b)) {
        apply ∧ᶜₑ₂ (++_to_∨ᶜ a b);
      };
      apply ⇒ᶜₑ tmp;
      apply ∨ᶜᵢ₁;
      apply Ha
    } {
      assume Hb;
      have tmp:  πᶜ ((⟇_to_∨ᶜ_rw a ∨ᶜ ⟇_to_∨ᶜ_rw b) ⇒ᶜ ⟇_to_∨ᶜ_rw (a ++ b)) {
        apply ∧ᶜₑ₂ (++_to_∨ᶜ a b);
      };
      apply ⇒ᶜₑ tmp;
      apply ∨ᶜᵢ₁;
      apply Ha
    }
  };
end;

opaque symbol bind_∃ [a p q]: (Π x, πᶜ (p x = q x))  → πᶜ ((`∃ᶜ (x: τ a), p x) = (`∃ᶜ (x: τ a), q x)) ≔
begin
  assume a p q H;
  apply prop_ext;
  apply ∧ᶜᵢ 
  {
    apply ⇒ᶜᵢ;
    assume H1;
    apply ∃ᶜₑ _ H1;
    assume x Hpx;
    apply ∃ᶜᵢ _ x;
    rewrite left (H x);
    apply Hpx;
  }
  {
    apply ⇒ᶜᵢ;
    assume H1;
    apply ∃ᶜₑ _ H1;
    assume x Hqx;
    apply ∃ᶜᵢ _ x;
    rewrite (H x);
    apply Hqx;
  };
end;

opaque symbol bind_∀ [a p q]: (Π (x: τ a), πᶜ (p x = q x))  → πᶜ ((`∀ᶜ (x: τ a), p x) = (`∀ᶜ (x: τ a), q x)) ≔
begin
  assume a p q H;
  apply prop_ext;
  apply ∧ᶜᵢ 
  {
    apply ⇒ᶜᵢ;
    assume H1;
    apply ∀ᶜᵢ _;
    assume x;
    have Hpx: πᶜ (p x) { apply ∀ᶜₑ x H1; };
    rewrite left (H x);
    apply Hpx;
  }
  {
    apply ⇒ᶜᵢ;
    assume H1;
    apply ∀ᶜᵢ _;
    assume x;
    have Hqx: πᶜ (q x) { apply ∀ᶜₑ x H1 };
    rewrite (H x);
    apply Hqx;
  };
end;

opaque symbol bind_∀' [a p q]: (Π (x: τ a), Π (y: τ a), πᶜ (x = y) → πᶜ (p x = q y))  → πᶜ ((`∀ᶜ (x: τ a), p x) = (`∀ᶜ (y: τ a), q y)) ≔
begin
  assume a p q;
  assume H;
  apply prop_ext;
  apply ∧ᶜᵢ 
  {
    apply ⇒ᶜᵢ;
    assume H1;
    apply ∀ᶜᵢ _;
    assume x;
    have Hpx: πᶜ (p x) { apply ∀ᶜₑ x H1; };
    rewrite left H x x (eq_reflᶜ x);
    apply Hpx
  }
  {
    apply ⇒ᶜᵢ;
    assume H1;
    apply ∀ᶜᵢ _;
    assume x;
    have Hqx: πᶜ (q x) { apply ∀ᶜₑ x H1 };
    rewrite H x x (eq_reflᶜ x);
    apply Hqx;
  };
end;

opaque symbol sko_forall [a p q]: (Π (x: τ a), πᶜ (x = `ϵ (y: τ a), ¬ (p y)) → πᶜ (p x = q))  → πᶜ ((`∀ᶜ (x: τ a), p x) = q) ≔
begin
  assume a p q H;
  apply prop_ext;
  apply ∧ᶜᵢ
  {
    apply ⇒ᶜₑ (∧ᶜₑ₂ (@contrapos (`∀ᶜ x, p x) q));
    apply ⇒ᶜᵢ;
    assume Hnq;
    rewrite .[x in ¬ x]  (ϵ_to_∀ p);
    have H1:  πᶜ (p (`ϵ x, ¬ (p x)) = q) { apply H; reflexivity };
    rewrite H1;
    apply Hnq
  }
  {
    rewrite .[x in _ ⇒ᶜ x]  (ϵ_to_∀ p);
    apply ⇒ᶜᵢ;
    assume Hq;
    have H1:  πᶜ (p (`ϵ y, ¬ (p y)) = q) { apply H; reflexivity };
    rewrite H1;
    apply Hq
  }
end;

// Inductive t A : nat -> Type :=
//   |nil : t A 0
//   |cons : forall (h:A) (n:nat), t A n -> t A (S n).
(a: Set) inductive Vec: ℕ → TYPE ≔
| □ : Vec a 0 // \Box
| cons [n: ℕ] : τ a →  Vec a n  →  Vec a (n + 1);

print Vec;

constant symbol vec : Set → ℕ → Set;
rule τ (vec $a $n) ↪ Vec $a $n;

symbol distinct [a] [n: τ nat]  : Vec a n → Prop; 

// // boolean case
rule @distinct _ 1 (cons _ □) ↪ ⊤
with @distinct _ 2 (cons $x (cons $y □)) ↪ ($x ≠ $y)
with @distinct _ (((_ +1) +1) +1) _ ↪ ⊥;

assert ⊢ distinct (cons a □) ≡ ⊤;
assert ⊢ distinct ((cons a (cons b □))) ≡ (a ≠ b);
assert ⊢ distinct (cons a (cons b (cons c □))) ≡ ⊥;
assert ⊢ distinct (cons a (cons b (cons c (cons d □)))) ≡ ⊥;


assert ⊢ distinct (cons 1 □) ≡ ⊤;
assert ⊢ distinct ((cons 1 (cons 2 □))) ≡ (1 ≠ 2);
assert ⊢ distinct (cons 1 (cons 2 (cons 3 □))) ≡ ⊥;

type 1;

opaque symbol distinct_elim  [a] [t: τ a] : πᶜ (distinct (cons t □) = ⊤) ≔ eq_reflᶜ (distinct(cons t □));

opaque symbol distinct_elim₂ [a] [x y: τ a] : πᶜ ((distinct ((cons x (cons y □)))) = (x ≠ y)) ≔ eq_reflᶜ (distinct (cons x (cons y □)));

opaque symbol distinct_elim₃ [a] [n: τ nat] [v: Vec a (n + 3)] : πᶜ (distinct v = ⊥) ≔  eq_reflᶜ (distinct v);


opaque symbol feqᶜ [a b] (f:τ a → τ b) [x x':τ a] : πᶜ(x = x') → πᶜ(f x = f x') ≔
begin
  assume a b f x x' xx'; rewrite xx'; reflexivity;
end;

opaque symbol feq2ᶜ [a b c] (f:τ a → τ b → τ c):
  Π [x x':τ a], πᶜ(x = x') → Π [y y':τ b], πᶜ(y = y') → πᶜ(f x y = f x' y') ≔
begin
  assume a b c f x x' xx' y y' yy'; rewrite xx'; rewrite yy'; reflexivity
end;

opaque symbol feq3ᶜ [a b c d] (f:τ a → τ b →  τ c → τ d):
  Π [x x':τ a], πᶜ(x = x') → Π [y y':τ b], πᶜ(y = y') → Π [z z':τ c], πᶜ(z = z') → πᶜ(f x y z = f x' y' z') ≔
begin
  assume a b c d f x x' xx' y y' yy' z z' zz'; rewrite xx'; rewrite yy'; rewrite zz'; reflexivity
end;


opaque symbol feq4ᶜ [a b c d e] (f:τ a → τ b →  τ c → τ d → τ e):
  Π [x1 x1':τ a], πᶜ(x1 = x1') →
  Π [x2 x2':τ b], πᶜ(x2 = x2') →
  Π [x3 x3':τ c], πᶜ(x3 = x3') →
  Π [x4 x4':τ d], πᶜ(x4 = x4') →
  πᶜ(f x1 x2 x3 x4 = f x1' x2' x3' x4') ≔
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

opaque symbol feq5ᶜ [a b c d e g] (f:τ a → τ b →  τ c  → τ d → τ e → τ g ):
  Π [x1 x1':τ a], πᶜ(x1 = x1') →
  Π [x2 x2':τ b], πᶜ(x2 = x2') →
  Π [x3 x3':τ c], πᶜ(x3 = x3') →
  Π [x4 x4':τ d], πᶜ(x4 = x4') →
  Π [x5 x5':τ e], πᶜ(x5 = x5') →
  πᶜ(f x1 x2 x3 x4 x5 = f x1' x2' x3' x4' x5') ≔
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
builtin "imp" ≔ ⇒ᶜ;
builtin "and" ≔ ∧ᶜ;
builtin "or"  ≔ ∨ᶜ;
builtin "not" ≔ ¬;
builtin "all" ≔ ∀ᶜ;
builtin "ex"  ≔ ∃ᶜ;
builtin "iff"  ≔ ⇔ᶜ;

opaque symbol cong_or [t1 t2 u1 u2: τ o]: π̇ (t1 = u1 ⟇ ▩) → π̇ (t2 = u2 ⟇ ▩) → π̇ (t1 ∨ᶜ t2 = u1 ∨ᶜ u2 ⟇ ▩) ≔
begin
  assume t1 t2 u1 u2 H1 H2;
  have H1': πᶜ (t1 = u1) { apply π̇ₗ H1 };
  have H2': πᶜ (t2 = u2) { apply π̇ₗ H2 };
  apply ∨ᶜᵢ₁;
  rewrite H1';
  rewrite H2';
   reflexivity
end;

opaque symbol cong_and [t1 t2 u1 u2: τ o]: π̇ (t1 = u1 ⟇ ▩) → π̇ (t2 = u2 ⟇ ▩) → π̇ (t1 ∧ᶜ t2 = u1 ∧ᶜ u2 ⟇ ▩) ≔
begin
  assume t1 t2 u1 u2 H1 H2;
  have H1': πᶜ (t1 = u1) { apply π̇ₗ H1 };
  have H2': πᶜ (t2 = u2) { apply π̇ₗ H2 };
  apply ∨ᶜᵢ₁;
  rewrite H1';
  rewrite H2';
   reflexivity
end;

opaque symbol cong_imp [t1 t2 u1 u2: τ o]: π̇ (t1 = u1 ⟇ ▩) → π̇ (t2 = u2 ⟇ ▩) → π̇ ((t1 ⇒ᶜ t2) = u1 ⇒ᶜ u2 ⟇ ▩) ≔
begin
  assume t1 t2 u1 u2 H1 H2;
  have H1': πᶜ (t1 = u1) { apply π̇ₗ H1 };
  have H2': πᶜ (t2 = u2) { apply π̇ₗ H2 };
  apply ∨ᶜᵢ₁;
  rewrite H1';
  rewrite H2';
   reflexivity
end;

constant symbol Mexp : TYPE;
symbol mexp : Set;
rule τ mexp ↪ Mexp;


associative commutative symbol Or : Mexp → Mexp → Mexp;
constant symbol Epsilon : Mexp;
symbol Var : 𝔹 → Prop → Mexp;

rule Or (Var true $t) (Var false $t) ↪ Epsilon
with Or (Var false $t) (Var true $t) ↪ Epsilon
with Or (Var true $t) (Or (Var false $t) $y) ↪ $y
with Or (Var false $t) (Or (Var true $t) $y) ↪ $y
with Or Epsilon $x ↪ $x
with Or $x Epsilon ↪ $x
;
//because of double negation, term such as  ¬¬ t ∨ ¬ t ↪ Var(false, ¬ t) ⊔ Var(false, t) do not reduce
// by adding these rules we rewrite it into ¬¬ t ∨ ¬ t ↪ Var(false, ¬ t) ⊔ Var(false, t) ↪ Var(true, t) ⊔ Var(false, t) ↪ Epsilon
rule (Var false (¬ $t)) ↪ (Var true $t)
with (Var true (¬ $t)) ↪ (Var false $t)
with (Var false ($t ⇒ ⊥)) ↪ (Var true $t)
with (Var true ($t ⇒ ⊥)) ↪ (Var false $t)
;

sequential symbol reify : Prop → Mexp;
rule reify (($x ∨ᶜ $z) ∨ᶜ $y) ↪ Or (Var true (($x ∨ᶜ $z))) (reify $y)
with reify ($x ∨ᶜ $y) ↪ Or (reify $x) (reify $y)
with reify (¬ $t) ↪ (Var false $t)
with reify ($t ⇒ ⊥) ↪ (Var false $t)
with reify $t ↪ (Var true $t)
;

symbol ind_Prop :
    Π x: τ o,
    Π p: (τ o → Prop),
    πᶜ (p ⊤) →
    πᶜ (p ⊥) 
    → (Π x0: τ o, πᶜ (p x0) → πᶜ (p (¬ x0)))
    → (Π x0: τ o, πᶜ (p x0) → Π x1: τ o, πᶜ (p x1) → πᶜ (p (x0 ∧ x1)))
    → (Π x0: τ o, πᶜ (p x0) → Π x1: τ o, πᶜ (p x1) → πᶜ (p (x0 ∨ x1)))
    → πᶜ (p x);

symbol eqb: 𝔹 → 𝔹 → 𝔹;
rule eqb true true ↪ true
with eqb true false ↪ false
with eqb false true ↪ false
with eqb false false ↪ true
;

symbol =c: Mexp → Mexp → 𝔹; notation =c infix 10;
rule (Var $b1 $x) =c (Var $b2 $y) ↪ (eq $x $y) Stdlib.Bool.and (eqb $b1 $b2)
with Epsilon =c Epsilon ↪ true
with Epsilon =c (Var _ _) ↪ false
with Epsilon =c Or _ _ ↪ false
with (Var _ _) =c Epsilon ↪ false
with (Or _ _) =c Epsilon ↪ false
with (Or $a $b)  =c (Or $c $d) ↪ ($a =c $c) Stdlib.Bool.and ($b =c $d)
;


sequential symbol reifyC  : Clause → Mexp;
rule reifyC (($x ⇒ ⊥) ⟇ $y) ↪ Or (Var false $x) (reifyC $y)
with reifyC ($x ⟇ $y) ↪ Or (Var true $x) (reifyC $y)
with reifyC ▩ ↪ Epsilon
;

opaque symbol eq_correct:  πᶜ (`∀ᶜ x, `∀ᶜ y, istrue (eq x y) ⇒ᶜ x = y) ≔
begin apply ∀ᶜᵢ; assume x; apply ∀ᶜᵢ; assume y; simplify; apply ⇒ᶜᵢ; assume Heq; apply ⊥ᶜₑ Heq end; //FIXME: stop RW

opaque symbol eq_complete:  πᶜ (`∀ᶜ x, `∀ᶜ y, (x = y) ⇒ᶜ istrue (eq x y)) ≔
begin
  apply ∀ᶜᵢ; assume x; apply ∀ᶜᵢ; assume y;
  apply ⇒ᶜᵢ; assume Hxeqy;
  rewrite Hxeqy;
  apply trivial
end;

opaque symbol and_elim1 [p q : τ bool] : πᶜ (istrue (p Stdlib.Bool.and q)) → πᶜ (istrue p) ≔
begin
  admit
end;

opaque symbol and_elim2 [p q : τ bool] : πᶜ (istrue (p Stdlib.Bool.and q)) → πᶜ (istrue q) ≔
begin
  admit
end;

opaque symbol eq_clause [x y: Clause] : πᶜ (x = y) → π̇ x  → π̇ y ≔
begin
    simplify;
    assume x y H H1;
    rewrite left H;
    apply H1
end;

symbol ind_ℂ : Π p: (Clause → Prop), πᶜ (p ▩) → (Π x0: τ o, Π x1: Clause, πᶜ (p x1) → πᶜ (p (x0 ⟇ x1))) → πᶜ (`∀ᶜ (x: τ clause), p x);

opaque symbol reify_correct :  πᶜ (`∀ᶜ x, `∀ᶜ y, istrue ( eq x y ) ⇒ᶜ x = y) →  πᶜ (`∀ᶜ a: τ clause, `∀ᶜ b: τ clause,  (istrue (reifyC a =c reifyC b)) ⇒ᶜ a = b) ≔
begin
  assume eq_correct;
  refine ind_ℂ (λ u, `∀ᶜ b, (istrue (reifyC u =c reifyC b)) ⇒ᶜ (u = b)) _ _
  {
    refine ind_ℂ (λ u, (istrue (reifyC ▩ =c reifyC u)) ⇒ᶜ (▩ = u)) _ _
    { apply ⇒ᶜᵢ; reflexivity }
    {  assume x xs H; simplify; apply ⇒ᶜᵢ; assume ▩≠⟇; apply ⊥ᶜₑ ▩≠⟇ }
  }
  {
    assume x xs IH;
    refine ind_ℂ (λ u, (istrue (reifyC (x ⟇ xs) =c reifyC u)) ⇒ᶜ ((x ⟇ xs) = u)) _ _
    { simplify; simplify; apply ⇒ᶜᵢ; assume ▩≠⟇; apply ⊥ᶜₑ ▩≠⟇ }
    {
      assume y ys _; apply ⇒ᶜᵢ; assume H;
      refine (@feq2ᶜ o clause clause (⟇) x y _ xs ys _)
      { 
        apply ⇒ᶜₑ (∀ᶜₑ y (∀ᶜₑ x eq_correct));
        apply (@and_elim2 (reifyC xs =c reifyC ys) (eq x y Stdlib.Bool.and eqb true true) H);
      }
      {
        refine ⇒ᶜₑ (∀ᶜₑ ys IH) (@and_elim1 (reifyC xs =c reifyC ys) (eq x y Stdlib.Bool.and eqb true true) H);
      }
    }
  }
end;

symbol reify_correct2 [a b: Clause]:   πᶜ (((reifyC a) =c (reifyC b)) = true) → πᶜ (a = b) ≔
begin
  assume a b H;
  have G: πᶜ (istrue (reifyC a =c reifyC b)) → πᶜ (a = b) {
    refine  ⇒ᶜₑ (∀ᶜₑ b (∀ᶜₑ a (reify_correct eq_correct)));
  };
  apply G;
  rewrite H;
  apply trivial
end;

// head

symbol head : τ o → Clause → τ o;

rule head $x ▩ ↪ $x
with head _ ($x ⟇ _) ↪ $x;

symbol behead  : Clause → Clause;

rule behead ▩ ↪ ▩
with behead (_ ⟇ $l) ↪ $l;

opaque symbol ⟇_inj [x:τ o] [l y m] : πᶜ ((x ⟇ l) = (y ⟇ m)) → πᶜ ((x = y) ∧ᶜ (l = m)) ≔
begin
  assume x l y m e; apply ∧ᶜᵢ { apply feqᶜ (head x) e } { apply feqᶜ behead e }
end;

print istrue_and;
symbol istrue_andᶜ : Π [p: 𝔹], Π [q: 𝔹], πᶜ (istrue p ∧ᶜ istrue q) → πᶜ (istrue (p Stdlib.Bool.and q));

opaque symbol reify_complete : πᶜ (`∀ᶜ x, `∀ᶜ y, (x = y) ⇒ᶜ istrue (eq x y)) →  πᶜ (`∀ᶜ (a: τ clause), `∀ᶜ (b: τ clause), (a = b) ⇒ᶜ (istrue (reifyC a =c reifyC b))) ≔
begin
  assume eq_complete;
   refine (ind_ℂ (λ u, `∀ᶜ b, (u = b) ⇒ᶜ istrue (reifyC u =c reifyC b)) _ _)
   {
      apply ∀ᶜᵢ; assume b;  apply ⇒ᶜᵢ; simplify; assume H▩=b; rewrite left H▩=b; simplify; apply trivial;
   }
   {
      assume x xs h;
      refine (ind_ℂ (λ u, ((x ⟇ xs) = u) ⇒ᶜ istrue (reifyC (x ⟇ xs) =c reifyC u)) _ _)
      {
        apply ⇒ᶜᵢ; assume Hxxs=▩; rewrite Hxxs=▩; apply trivial
      }
      {
        assume y ys H;
        apply ⇒ᶜᵢ;
        assume H2;
        have G: πᶜ ((x = y) ∧ᶜ (xs = ys)) { apply ⟇_inj H2 };
        have G1: πᶜ (x = y ) { apply ∧ᶜₑ₁  G };
        have G2: πᶜ (xs = ys) { apply ∧ᶜₑ₂  G };
        simplify =c;
        apply @istrue_andᶜ (reifyC xs =c reifyC ys) (Var true x =c Var true y);
        apply ∧ᶜᵢ
        { refine ⇒ᶜₑ (∀ᶜₑ ys h) G2 }
        { simplify =c;   refine ⇒ᶜₑ (∀ᶜₑ y (∀ᶜₑ x eq_complete)) G1;  }
      }
   }
end;

opaque symbol pack [a b] : π̇ a → π̇ b → π̇ (a ++ b) ≔ begin
    assume a b Ha Hb; 
    simplify; 
    apply Clause_ind (λ u, ⟇_to_∨ᶜ_rw (u ++ b)) a
    { simplify; apply Hb  }
    {
        assume x l IH;
        simplify;
        apply ∨ᶜᵢ₂;
        apply IH
    }
end;

notation ≥ infix 10;
