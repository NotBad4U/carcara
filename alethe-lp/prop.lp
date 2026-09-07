// Alethe rules whose conclusion is a propositional tautology or a Boolean
// rewrite, the *_simplify family for Boolean connectives, and the cvc5 RARE
// Boolean rewrites. Required by every generated proof.
require open alethe.core;
require open Stdlib.List;
require Stdlib.String;
opaque symbol neg_⊥ : π (¬ ⊥) ≔ begin refine (λ x, x) end;

// # Clause
// Clauses are encoded with list à la Church Encoding.
// This encoding is necessary because Inductive type in Lambdapi
// could not live in Prop.
opaque symbol ite1' [c t e] : π (ite c t e ⇒ c ∨ e) ≔
begin
  assume c t e;
  refine ite_ind c t e (λ u, u ⇒ (c ∨ e)) _ _
  {
    assume Hc;
    
    assume Ht;
    apply ∨ᵢ₁;
    apply Hc
  }
  {
    assume Hnc;
    
    assume He;
    apply ∨ᵢ₂;
    apply He
  }
end;

opaque symbol ite1 (c t e: τ o) : π (ite c t e) → π̇ (c ⸬ e ⸬ □) ≔
begin
  assume c t e H;
  simplify;
  rewrite or_identity_r;
  apply ( (@ite1' c t e)) H;
end;

opaque symbol ite2' [c t e] : π (ite c t e ⇒ ((¬ c) ∨ t)) ≔
begin
  assume c t e;
  refine ite_ind c t e (λ u, u ⇒ (¬ c ∨ t)) _ _
  {
    assume Hc;
    
    assume Ht;
    apply ∨ᵢ₂;
    apply Ht
  }
  {
    assume Hc;
    
    assume He;
    remove He;
    apply ∨ᵢ₁;
    simplify;
    refine Hc
  };
end;

opaque symbol ite2 (c t e: τ o) : π (ite c t e) → π̇ ((¬ c) ⸬ t ⸬ □) ≔
begin
  assume c t e H;
  simplify;
  rewrite or_identity_r;
  apply ( (@ite2' c t e)) H;
end;

// Use it to unfold the definition of `¬`.
// The tactic simplify is to agressive.
opaque symbol ite_pos1 [c t e] : π̇ ((¬ (ite c t e)) ⸬ c ⸬ e ⸬ □) ≔
begin
  assume c t e;
  apply imply_to_or;
  
  assume H;
  simplify;
  rewrite or_identity_r;
  apply ( (@ite1' c t e)) H;
end;

opaque symbol ite_pos2 [c t e] : π̇ (¬ (ite c t e) ⸬ ¬ c ⸬ t ⸬ □) ≔
begin
  assume c t e;
  apply imply_to_or;
  
  assume H;
  simplify;
  rewrite or_identity_r;
  apply ( (@ite2' c t e)) H;
end;

opaque symbol ite_neg1 [c t e] : π̇ ((ite c t e) ⸬ c ⸬ ¬ e ⸬ □) ≔
begin
  assume c t e;
  simplify;
  rewrite or_identity_r;
  apply ite_ind c t e (λ u, u ∨ (c ∨ (e ⇒ ⊥)))
  {
    assume Hc; apply ∨ᵢ₂; apply ∨ᵢ₁; refine Hc
  }
  {
    assume Hnc; rewrite ∨_com;
    rewrite ∨_assoc;
    apply ∨ᵢ₂;
    rewrite ∨_com;
    apply em;
  };
end;

opaque symbol ite_neg2 [c t e] : π̇ ((ite c t e) ⸬ ¬ c ⸬ ¬ t ⸬ □) ≔
begin
  assume c t e;
  simplify;
  rewrite or_identity_r;
  apply ite_ind c t e (λ u, u ∨ ((c ⇒ ⊥)∨ (t ⇒ ⊥)))
  {
    assume Hnc; rewrite ∨_com;
    rewrite ∨_assoc;
    apply ∨ᵢ₂;
    rewrite ∨_com;
    apply em;
  }
  {
    assume Hc; apply ∨ᵢ₂; apply ∨ᵢ₁; refine Hc
  }
end;

opaque symbol not_ite1' [c t e] : π (¬ (ite c t e) ⇒ c ∨ ¬ e) ≔
begin
  assume c t e;
  refine ite_ind c t e (λ u, ¬ u ⇒ c ∨ ¬ e) _ _
  {
    assume Hc;
    
    assume Hnt;
    apply ∨ᵢ₁;
    refine Hc;
  }
  {
    assume Hcimpbot;
    
    assume Hne;
    apply ∨ᵢ₂;
    refine Hne
  }
end;

opaque symbol not_ite1 [c t e] : π (¬ (ite c t e)) → π̇( c ⸬ ¬ e ⸬ □) ≔
begin
  assume c t e H;
  simplify;
  rewrite or_identity_r;
  apply ( (@not_ite1' c t e) H);
end;

opaque symbol not_ite2' [c t e] : π (¬ (ite c t e) ⇒ ¬ c  ∨ ¬ t) ≔
begin
  assume c t e;
  refine ite_ind c t e (λ u, ¬ u ⇒ ¬ c  ∨ ¬ t) _ _
  { assume Hc;  assume Hnt; apply ∨ᵢ₂; refine Hnt }
  { assume Hcimpbot;  assume Hne; apply ∨ᵢ₁; simplify; refine Hcimpbot; }
end;

opaque symbol not_ite2 [c t e] : π (¬ (ite c t e)) → π̇(¬ c ⸬ ¬ t ⸬ □) ≔
begin
  assume c t e H;
  simplify;
  rewrite or_identity_r;
  apply ( (@not_ite2' c t e) H);
end;

symbol xor a b ≔ ((¬ a) ∧ b) ∨ (a ∧ (¬ b));

opaque symbol xor_pos1 [a b] : π̇ (¬ (xor a b) ⸬ a ⸬ b ⸬ □) ≔
begin
  assume a b;
  simplify;
  apply imply_to_or;
  
  assume H;
  apply ∨ₑ H
  { assume Hnab; apply ∨ᵢ₂;  apply ∨ᵢ₁; apply ∧ₑ₂ Hnab }
  { assume Hnab; apply ∨ᵢ₁; apply ∧ₑ₁ Hnab }
end;

opaque symbol xor_pos2 [a b] : π̇ (¬ (xor a b) ⸬ ¬ a ⸬ ¬ b ⸬ □) ≔
begin
  assume a b;
  simplify;
  apply imply_to_or;
  
  assume H;
  apply ∨ₑ H
  { assume Hnab; apply ∨ᵢ₁; apply ∧ₑ₁ Hnab }
  { assume Hnab; apply ∨ᵢ₂;  apply ∨ᵢ₁; apply ∧ₑ₂ Hnab }
end;

opaque symbol xor_neg1 [a b] : π̇ ((xor a b) ⸬ a ⸬ ¬ b ⸬ □) ≔
begin
  simplify;
  assume a b;
  rewrite ∨_assoc;
  rewrite ∨_com;
  rewrite distributive_or;
  apply ∧ᵢ
  {
    rewrite or_identity_r;
    rewrite ∨_assoc;
    apply ∨ᵢ₂;
    rewrite ∨_com;
    rewrite left ∨_assoc;
    apply ∨ᵢ₁;
    rewrite ∨_com;
    apply em
  }
  {
    rewrite ∨_assoc;
    apply ∨ᵢ₂;
    rewrite ∨_assoc;
    apply ∨ᵢ₂;
    rewrite ∨_com;
    rewrite left ∨_assoc;
    apply ∨ᵢ₁;
    apply em
  }
end;

opaque symbol xor_neg2 [a b] : π̇ ((xor a b) ⸬ ¬ a ⸬ b ⸬ □) ≔
begin
  simplify;
  assume a b;
  rewrite ∨_assoc;
  rewrite ∨_com;
  rewrite distributive_or;
  apply ∧ᵢ
  {
    rewrite ∨_assoc;
    rewrite ∨_com;
    rewrite distributive_or;
    apply ∧ᵢ
    {
      rewrite ∨_assoc;
      apply ∨ᵢ₂;
      rewrite ∨_com;
      apply em
    }
    {
      rewrite ∨_com;
      rewrite left ∨_assoc;
      apply ∨ᵢ₁;
      rewrite ∨_com;
      rewrite ∨_assoc;
      apply ∨ᵢ₂;
      rewrite or_identity_r;
      apply em
    }
  }
  {
    rewrite ∨_assoc;
    rewrite ∨_com;
    rewrite distributive_or;
    apply ∧ᵢ
    {
      rewrite ∨_com;
      rewrite left ∨_assoc;
      apply ∨ᵢ₁;
      rewrite left ∨_assoc;
      apply ∨ᵢ₁;
      apply em
    }
    {
      rewrite ∨_com;
      rewrite left ∨_assoc;
      rewrite or_identity_r;
      apply ∨ᵢ₁;
      rewrite ∨_com;
      rewrite ∨_assoc;
      apply ∨ᵢ₂;
      apply em
    }
  }
end;

// // i ▷ 𝜑1 ∨ ⋯ ∨ 𝜑n
// // j ▷ 𝜑1 , ⋯ , 𝜑n
constant symbol or [a b] : π̇ ((a ∨ b) ⸬ □) → π̇ (∨_to_list  (a ∨ b));

opaque symbol implies [φ₁ φ₂] : π (φ₁ ⇒ φ₂) → π̇ (¬ φ₁ ⸬ φ₂ ⸬ □) ≔
begin
  assume φ₁ φ₂ Hφ₁⇒φ₂;
  apply imply_to_or;
  
  assume πφ₁;
  apply ∨ᵢ₁;
  apply  Hφ₁⇒φ₂ πφ₁
end;

opaque symbol not_implies1 [φ₁ φ₂] : π (¬ (φ₁ ⇒ φ₂)) → π̇ (φ₁ ⸬ □) ≔
begin
  assume φ₁ φ₂ Hnot_φ₁⇒φ₂;
  apply ∨ᵢ₁;
  apply ∧ₑ₁ (imply_to_and Hnot_φ₁⇒φ₂)
end;

opaque symbol not_implies2 [φ₁ φ₂] : π (¬ (φ₁ ⇒ φ₂)) →  π̇ (¬ φ₂ ⸬ □) ≔
begin
  assume φ₁ φ₂ Hnot_φ₁⇒φ₂;
  apply ∨ᵢ₁;
  apply ∧ₑ₂ (imply_to_and Hnot_φ₁⇒φ₂)
end;

opaque symbol implies_neg1 [φ₁ φ₂] : π̇ ((φ₁ ⇒ φ₂) ⸬ φ₁ ⸬ □) ≔
begin
  assume φ₁ φ₂;
  simplify;
  rewrite left imp_eq_or;
  rewrite left ∨_assoc;
  apply ∨ᵢ₁;
  rewrite .[(¬ φ₁) ∨ φ₂] ∨_com;
  rewrite ∨_assoc;
  apply ∨ᵢ₂;
  rewrite ∨_com;
  apply em
end;

opaque symbol implies_neg2 [φ₁ φ₂] : π̇ ((φ₁ ⇒ φ₂) ⸬ ¬ φ₂ ⸬ □) ≔
begin
  assume φ₁ φ₂;
  simplify;
  rewrite left imp_eq_or;
  rewrite left ∨_assoc;
  apply ∨ᵢ₁;
  rewrite ∨_assoc;
  apply ∨ᵢ₂;
  apply em
end;

opaque symbol equiv1 [φ₁ φ₂] : π̇ ((φ₁ = φ₂) ⸬ □) → π̇ ((¬ φ₁) ⸬ φ₂ ⸬ □) ≔
begin
  assume φ₁ φ₂ H1;
  apply ∨ₑ H1
  {
    assume Hequiv;
    have Hequiv':  π (φ₁ ⇔ φ₂) { apply ⟺_ext; apply Hequiv };
    have H2: π (φ₁ ⇒ φ₂) { apply ∧ₑ₁ Hequiv' };
    have H3: π (φ₂ ⇒ φ₁) { apply ∧ₑ₂ Hequiv' };
    have Hassoc: π (((¬ φ₁) ∨ (φ₂ ∨ ⊥)) ⇔  (((¬ φ₁) ∨ φ₂) ∨ ⊥)) {
      apply (@Stdlib.Prop.∨_assoc (¬ φ₁) φ₂ ⊥);
    };
    have Hassoc_left: π ((((¬ φ₁) ∨ φ₂) ∨ ⊥)  ⇒  ((¬ φ₁) ∨ (φ₂ ∨ ⊥))) {
      refine ∧ₑ₂ Hassoc
    };
    apply  Hassoc_left;
    apply ∨ᵢ₁;
    apply imply_to_or;
    refine H2;
  }
  {
    assume Hbot;
    apply ∨ᵢ₂;
    apply ∨ᵢ₂;
    apply Hbot;
  }
end;

opaque symbol equiv2 [φ₁ φ₂] : π̇ ((φ₁ = φ₂) ⸬ □)  → π̇ (φ₁ ⸬ (¬ φ₂) ⸬ □) ≔
begin
  assume φ₁ φ₂ H1;
  apply ∨ₑ H1
  {
    assume Hequiv;
    have Hequiv':  π (φ₁ ⇔ φ₂) { apply ⟺_ext; apply Hequiv };
    have H2: π (φ₁ ⇒ φ₂) { apply ∧ₑ₁ Hequiv' };
    have H3: π (φ₂ ⇒ φ₁) { apply ∧ₑ₂ Hequiv' };
    have Hassoc: π ((φ₁ ∨ ((¬ φ₂) ∨ ⊥)) ⇔  ((φ₁ ∨ (¬ φ₂)) ∨ ⊥)) {
      apply (@Stdlib.Prop.∨_assoc φ₁ (¬ φ₂) ⊥);
    };
    have Hassoc_left: π (((φ₁ ∨ (¬ φ₂)) ∨ ⊥)  ⇒  (φ₁ ∨ ((¬ φ₂) ∨ ⊥))) {
      refine ∧ₑ₂ Hassoc
    };
    apply  Hassoc_left;
    apply ∨ᵢ₁;
    rewrite ∨_com;
    apply imply_to_or;
    refine H3;
  }
  {
    assume Hbot;
    apply ∨ᵢ₂;
    apply ∨ᵢ₂;
    apply Hbot;
  }
end;

opaque symbol equiv_pos1 [φ₁ φ₂] : π̇ ((¬ (φ₁ = φ₂)) ⸬ φ₁ ⸬ ¬ φ₂ ⸬ □) ≔
begin
  simplify;
  assume p q;
  apply imply_to_or;
  assume Heq;
  rewrite Heq;
  rewrite left ∨_assoc;
  apply ∨ᵢ₁;
  apply em
end;

opaque symbol equiv_pos2 [φ₁ φ₂] : π̇ ((¬ (φ₁ = φ₂)) ⸬ (¬ φ₁) ⸬ φ₂ ⸬ □) ≔
begin
  simplify;
  assume p q;
  apply imply_to_or;
  assume Heq;
  rewrite or_identity_r;
  rewrite ∨_com;
  rewrite Heq;
  apply em
end;

opaque symbol equiv_neg1 [φ₁ φ₂] : π̇ ((φ₁ = φ₂) ⸬ ¬ φ₁ ⸬ ¬ φ₂ ⸬ □) ≔
begin
  simplify;
  assume p q;
  rewrite or_identity_r;
  rewrite ∨_com;
  rewrite ∨_assoc;
  apply imply_to_or;
  
  assume Hp;
  apply imply_to_or;
  
  assume Hq;
  apply prop_ext;
  apply ∧ᵢ
  {  assume Hp'; apply Hq }
  {  assume Hq'; apply Hp }
end;

opaque symbol equiv_neg2 [φ₁ φ₂] : π̇ ((φ₁ = φ₂) ⸬ φ₁ ⸬ φ₂ ⸬ □) ≔
begin
  simplify;
  assume p q;
  rewrite or_identity_r;
  rewrite left iff_equiv_eq;
  rewrite ∨_com;
  simplify;
  rewrite distributive_or; //(p ∨ q) (p ⇒ q) (q ⇒ p);
  apply ∧ᵢ
  {
    rewrite left imp_eq_or;
    rewrite ∨_assoc;
    rewrite .[(¬ p) ∨ q] ∨_com;
    rewrite left  .[q ∨ (q ∨ ¬ p)] ∨_assoc;
    rewrite or_idempotent;
    rewrite .[q ∨ (¬ p)] ∨_com;
    rewrite left ∨_assoc;
    apply ∨ᵢ₁;
    apply em
  }
  {
    rewrite left imp_eq_or;
    rewrite left ∨_assoc;
    rewrite .[p ∨ q] ∨_com;
    rewrite .[((q ∨ p) ∨ ¬ q)] ∨_assoc;
    apply ∨ᵢ₁;
    rewrite .[p ∨ ¬ q] ∨_com;
    rewrite left ∨_assoc;
    apply ∨ᵢ₁;
    apply em
  }
end;

opaque symbol implies_pos [φ₁ φ₂] : π̇ ((¬ (φ₁ ⇒ φ₂)) ⸬ ¬ φ₁ ⸬ φ₂ ⸬ □) ≔
begin
  simplify;
  assume x y;
  rewrite or_identity_r;
  rewrite left imp_eq_or (x ⇒ y) ⊥;
  rewrite left imp_eq_or x ⊥;
  rewrite left imp_eq_or;
  rewrite or_identity_r;
  rewrite or_identity_r;
  rewrite ∨_com;
  refine @em ((x ⇒ ⊥) ∨ y)
end;

symbol ∧ₑₙ k l : π (k ∈ₙ (indexes l)) → π̇ (conj l ⸬ □) → π̇ ((literal l k ) ⸬ □) ≔
begin
  assume k l h1 h2;
  simplify;
  rewrite or_identity_r;
  refine select k l h1 (π̇ₗ h2)
end;


// (and_pos) ⊢ ¬ (x1 ∧ ... ∧ xn), xk ≡ (x1 ∧ ... ∧ xn) ⊢ xk
opaque symbol and_pos_aux (id : τ nat) (cnf: 𝕃 o) : π (id ∈ₙ (indexes cnf)) → π (¬ (conj cnf) ∨ (literal cnf id)) ≔
begin
  assume id cnf h;
  rewrite imp_eq_or;
  assume hconj;
  refine select id cnf h hconj 
end;

// Rule and_pos: ¬(𝜑1 ∧ … ∧ 𝜑𝑛), 𝜑𝑘
// (and_pos) ⊢ ¬ (x1 ∧ ... ∧ xn), xk ≡ (x1 ∧ ... ∧ xn) ⊢ xk
opaque symbol and_pos (k : τ nat) (cnf: 𝕃 o) : π (k ∈ₙ (indexes cnf)) → π̇ (¬ (conj cnf) ⸬ (literal cnf k) ⸬ □) ≔
begin
  assume k cnf h;
  simplify;
  rewrite or_identity_r;
  refine and_pos_aux k cnf h
end;

opaque symbol morgan (l: 𝕃 o) : π ((¬ (disj l)) = conj (negate l)) ≔
begin
induction
{
  simplify;
  apply prop_ext;
  apply ∧ᵢ { assume h; apply ⊤ᵢ } { assume h; refine (λ x, x) }
}
{
  assume h tl IH;
  rewrite left disj_eq;
  rewrite morgan2;
  rewrite IH;
  simplify;
  rewrite conj_eq;
  reflexivity
}
end;

opaque symbol morganN2 (l: 𝕃 o) : π ((¬ (conj l)) = disj (negate l)) ≔
begin
induction
{
  simplify;
  apply prop_ext;
  apply ∧ᵢ { assume h; apply h ⊤ᵢ } { assume h; apply ⊥ₑ h }
}
{
  assume h tl IH;
  simplify;
  rewrite left conj_eq;
  rewrite left IH;
  have foldneg: Π e, π (¬ e = (e ⇒ ⊥)) { reflexivity };
  rewrite left foldneg;
  rewrite morgan1 h (conj tl);
  reflexivity
}
end;

opaque symbol select_disj (id : τ nat) (l: 𝕃 o) : 
    π (id ∈ₙ (indexes (negate l))) → π (¬ (disj l)) → π (literal (negate l) id) ≔
begin
  assume id l H Hdisj;
  have g: π (conj (negate l)) { rewrite left morgan l; refine Hdisj };
  refine select id (negate l) H g;
end;

// Rule not_or:
// i. ▷ ¬(𝜑1 ∨ ⋯ ∨ 𝜑𝑛)
// j. ▷ ¬𝜑𝑘
opaque symbol not_or (id : τ nat) (l: 𝕃 o) : 
    π (id ∈ₙ (indexes (negate l))) → π (¬ (disj l)) → π̇ (literal (negate l) id ⸬  □) ≔
begin
  assume id l H Hdisj;
  apply ∨ᵢ₁;
  have g: π (conj (negate l)) { rewrite left morgan l; refine Hdisj };
  refine select id (negate l) H g;
end;


opaque symbol not_and_aux (l: 𝕃 o) : 
    π (¬ (conj l)) → π (disj (negate l)) ≔
begin
  induction
  { assume H; refine H ⊤ᵢ }
  {
    assume x xs IH Hconj;
    simplify;
    have g: π (¬ (x ∧  conj xs)) {
      rewrite conj_eq;
      refine Hconj;
    };
    have g2: π (¬ x ∨  ¬ conj xs) { rewrite left morgan1; refine g };
    apply ∨ₑ g2 
    { assume Hnx; apply ∨ᵢ₁; refine Hnx; }
    { assume Hnxs; apply ∨ᵢ₂; refine IH Hnxs }
  }
end;

// i. ▷ ¬(𝜑1 ∧ … ∧ 𝜑𝑛)
// j. ▷ ¬𝜑1, … , ¬𝜑𝑛
opaque symbol not_and (l: 𝕃 o) : 
    π (¬ (conj l)) → π̇ (negate l) ≔
begin
  simplify;
  assume l h;
  refine not_and_aux l h;
end;

// assert c0 c1 c2 c2' ⊢ not_and_k (c0 ⸬ c1 ⸬ c2 ⸬ c1 ⸬ □): 
//     π (¬ (c0 ∧ c1 ∧ c2 ∧ c1)) → π ((¬ c0) ∨ (¬ c1) ∨ (¬ c2) ∨ (¬ c1));

// or_pos: ⊢ ¬ (x1 ∨ ... ∨ xn) ∨ x1 ∨ ... ∨ xn
opaque symbol or_pos_aux (l: 𝕃 o) : π (¬ (disj l) ∨ (disj l)) ≔
begin
  assume l;
  rewrite ∨_com;
  apply em
end;


// Rule or_pos:  ¬(𝜑1 ∨ ⋯ ∨ 𝜑𝑛), 𝜑1 , … , 𝜑𝑛
opaque symbol or_pos (l: 𝕃 o) :  π̇ ((¬ (disj l)) ⸬ l) ≔
begin
  assume l;
  simplify;
  rewrite ∨_com;
  apply em
end;

// and_neg: ⊢  (x1 ∧ ... ∧ xn) ∨ ¬ x1 ∨ ... ∨ ¬ xn
opaque symbol and_neg_aux (l: 𝕃 o) : π ((conj l) ∨ disj (negate l)) ≔
begin
  assume l;
  rewrite left morganN2 l;
  refine em (conj l);
end;

opaque symbol and_neg [c] (l: 𝕃 o) : π (disj c = disj (negate l)) → π̇ ((conj l) ⸬ c) ≔
begin
  assume c l h;
  simplify;
  rewrite h;
  refine and_neg_aux l
end;


opaque symbol lit_imp_disj (c: 𝕃 o) (ks: 𝕃 nat) : 
    π (`∃ x, literal c x ∧ x ∈ₙ ks) → π (disj (literals c ks)) ≔
begin
    assume c;
    induction
    {assume h1;
        have H0: Π x: τ nat, π ((λ x1, literal c x1 ∧ ⊥) x) → π ⊥
        {assume x h2;
        refine ∧ₑ₂ h2};
        refine ∃ₑ h1 H0}
    {assume n l h1 h2;
        have H1: Π x: τ nat,
        π ((λ x1, literal c x1 ∧ (eqn x1 n Stdlib.Bool.or x1 ∈ₙ l)) x)
            → π (disj (literal c n ⸬ literals c l))
        {assume m h3;
        have H0: π (eqn m n ∨ m ∈ₙ l)
            {refine ∨_istrue [eqn m n] [m ∈ₙ l] (∧ₑ₂ h3)};
        have H1: π (eqn m n) → π (disj (literal c n ⸬ literals c l))
            {assume h4;
            have H1_0: π (literal c n)
                {have H1_0_0: π (n = m)
                {symmetry;
                refine eqn_correct m n h4};
                rewrite H1_0_0;
                refine ∧ₑ₁ h3};
            refine disj_head (literal c n) (literals c l) H1_0};
        have H2: π (m ∈ₙ l) → π (disj (literal c n ⸬ literals c l))
            {assume h4;
            have H2_0: π (`∃ x, literal c x ∧ x ∈ₙ l)
                {have H2_0_0: π ((λ x, literal c x ∧ x ∈ₙ l) m)
                {refine ∧ᵢ (∧ₑ₁ h3) h4};
                refine ∃ᵢ m H2_0_0};
            refine disj_tail (literal c n) (literals c l) (h1 H2_0)};
        refine ∨ₑ H0 H1 H2};
        refine ∃ₑ h2 H1}
end;

assert c0 c1 c2 c2' ⊢ lit_imp_disj (c0 ⸬ c1 ⸬ c2 ⸬ c1 ⸬ □) (indexes (c0 ⸬ c1 ⸬ c2 ⸬ c1 ⸬ □)): 
    π (`∃ x, literal (c0 ⸬ c1 ⸬ c2 ⸬ c1 ⸬ □) x ∧ x ∈ₙ (indexes (c0 ⸬ c1 ⸬ c2 ⸬ c1 ⸬ □))) → π (disj (literals (c0 ⸬ c1 ⸬ c2 ⸬ c1 ⸬ □) (indexes (c0 ⸬ c1 ⸬ c2 ⸬ c1 ⸬ □))));


// or_neg  (x1 ∨ ... ∨ xn) ∨ ¬ xk ≡ ¬ xk ∨ (x1 ∨ ... ∨ xn) ≡  xk ⇒ (x1 ∨ ... ∨ xn) ≡ xk ⊢  (x1 ∨ ... ∨ xn)
opaque symbol or_neg_aux id (l: 𝕃 o) : 
    π (literal l id ∧ id ∈ₙ (indexes l)) → π (disj l) ≔
begin
  assume id l h;
  have g: π (disj (literals l (indexes l)))
  {
    refine lit_imp_disj l (indexes l) _;
    refine ∃ᵢ id _;
    refine h
  };
  rewrite left nths_indexes_id ⊥ l;
  refine g
end;

// Rule or_neg (𝜑1 ∨ … ∨ 𝜑𝑛), ¬𝜑
// However, this lemma prove ¬𝜑, (𝜑1 ∨ … ∨ 𝜑𝑛)
// The litteral ¬𝜑
opaque symbol or_neg [c] k (l: 𝕃 o) : π ((disj c) = (disj l)) →
    π (k ∈ₙ (indexes l)) → π̇ ((¬ (literal l k )) ⸬ c) ≔
begin
  assume c k l h h2;
  simplify;
  // rewrite ∨_com;
  rewrite h;
  change π ((¬ nth ⊥ l k) ∨ disj l);
  rewrite imp_eq_or;
  assume hlit;
  refine or_neg_aux k l _ ;
  apply ∧ᵢ
  { refine hlit }
  { refine h2 }
end;

symbol ∨ₑₙ (l : 𝕃 o) : π̇ ((disj l) ⸬ □) → π̇ l ≔ π̇ₗ;

/* ------------------------------------------------------------------------
   Alethe *_simplify rules (was alethe.Simplify)
   ------------------------------------------------------------------------ */

builtin "String" ≔ Stdlib.String.String;

// Rule 71: equiv_simplify

symbol equiv_simplify1 p q : π (((¬ p) = ¬ q) = (p = q)) ≔
begin
    assume p q;
    apply prop_ext;
    apply ∧ᵢ
    {
        assume Heq;
        apply prop_ext; 
        apply ∧ᵢ
        {
            rewrite left imp_eq_or;
            rewrite Heq;
            rewrite ∨_com;
            apply em
        }
        {
            rewrite left imp_eq_or;
            rewrite left Heq;
            rewrite ∨_com;
            apply em
        }
    }
    {
        assume Heq;
        rewrite Heq;
        reflexivity
    }
end;

symbol equiv_simplify2  (p : τ o) : π ((p = p) = ⊤) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᵢ
    { assume H; remove H; apply ⊤ᵢ  }
    { assume H⊤; remove H⊤; reflexivity }
end;

// (𝜑 ≈ ¬ 𝜑) ⇒ ⊥
symbol equiv_simplify3 p : π ((p = (¬ p)) = ⊥) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left iff_equiv_eq;
    simplify;
    rewrite left imp_eq_or;
    rewrite left imp_eq_or;
    rewrite left imp_eq_or;
    rewrite left imp_eq_or;
    apply ∧ᵢ
    {
        rewrite or_identity_r;
        rewrite or_identity_r;
        rewrite morgan1;
        rewrite .[¬ ((¬ (¬ p)) ∨ p)] morgan2;
        rewrite distributive_or;
        rewrite or_idempotent;
        apply ∧ᵢ
        {
            apply em
        }
        {
            rewrite ∨_com;
            apply em
        };
    }
    {   
        assume contra;
        refine ⊥ₑ contra
    }
end;

// (¬ 𝜑 ≈ 𝜑) ⇒ ⊥
symbol equiv_simplify4 p : π (((¬ p) = p) = ⊥) ≔
begin
    assume p;
    rewrite =_sym (¬ p) p;
    apply equiv_simplify3
end;

//(⊤ ≈ 𝜑) ⇒ 𝜑
symbol equiv_simplify5 p : π ((⊤ = p) = p) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left iff_equiv_eq;
    apply ∧ᵢ
    {
        assume H;
        have H2: π (⊤ ⇒ p) { apply ∧ₑ₁ H };
        apply H2;
        apply ⊤ᵢ
    }
    {
        assume Hp;
        apply ∧ᵢ
        { assume Htop; apply Hp }
        { assume Hp'; apply ⊤ᵢ }
    }
end;


// (𝜑 ≈ ⊤) ⇒ 𝜑
symbol equiv_simplify6 p : π ((p = ⊤) = p) ≔
begin
    assume p;
    rewrite =_sym p ⊤;
    apply equiv_simplify5
end;

// (⊥ ≈ 𝜑) ⇒ ¬ 𝜑
symbol equiv_simplify7 p : π ((⊥ = p) = ¬ p) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left iff_equiv_eq;
    simplify;
    apply ∧ᵢ
    { assume h; refine ∧ₑ₂ h }
    { assume h; apply ∧ᵢ { assume contra; refine ⊥ₑ contra } { refine h } }
end;

// (𝜑 ≈ ⊥) ⇒ ¬ 𝜑
symbol equiv_simplify8 p : π ((p = ⊥) = ¬ p) ≔
begin
    assume p;
    rewrite =_sym  p ⊥;
    apply equiv_simplify7
end;

symbol all_equiv_simplify ≔ 
    (#rewrite equiv_simplify1) ⸬ (#rewrite equiv_simplify2) ⸬ (#rewrite equiv_simplify3)
    ⸬ (#rewrite equiv_simplify4) ⸬(#rewrite equiv_simplify5) ⸬ (#rewrite equiv_simplify6) ⸬ (#rewrite equiv_simplify7) ⸬  (#rewrite equiv_simplify8) ⸬  □;

symbol equiv_simplify ≔ #repeat (applyAny all_equiv_simplify) and #try (#reflexivity #orelse (#apply ⊤ᵢ));


// Rule 69: not_simplify

opaque symbol not_simplify1 t : π ((¬ ¬ t) = t) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    {
        rewrite nnpp_eq;
        assume Ht;
        apply Ht
    }
    {
        rewrite nnpp_eq;
        assume Ht;
        apply Ht
    }
end;

opaque symbol not_simplify2 : π (¬ ⊥ = ⊤) ≔
begin
    simplify;
    apply prop_ext;
    apply ∧ᵢ
    { assume H; apply ⊤ᵢ }
    { assume Htop Hbot; refine Hbot }
end;

opaque symbol not_simplify3 : π (¬ ⊤ = ⊥) ≔
begin
    simplify;
    apply prop_ext;
    apply ∧ᵢ
    { assume H; apply fold_⇒ H; apply ⊤ᵢ }
    { assume Hbot; apply ⊥ₑ; refine Hbot }
end;

symbol all_not_simplify ≔ (#rewrite not_simplify1) ⸬ (#rewrite not_simplify2) ⸬ (#rewrite not_simplify3) ⸬ □;

symbol not_simplify ≔ #repeat (applyAny all_not_simplify) and #try (#reflexivity #orelse (#apply ⊤ᵢ));

private symbol not_simplify_test : π ((¬ ¬ ¬ ¬ ¬ ¬ ⊤) = (¬ ⊥)) ≔ begin
eval not_simplify;
end;

// Rule 70: implies_simplify

opaque symbol implies_simplify1 p q : π ((¬ p ⇒ ¬ q) = (q ⇒ p)) ≔
begin
    assume p q;
    apply prop_ext;
    apply ∧ᵢ
    { 
        assume H; rewrite left imp_eq_or;
        have H1: π ((¬ ¬ p) ∨ ¬ q) { rewrite imp_eq_or; refine H };
        apply ∨ₑ H1
        { assume Hnnp;  apply ∨ᵢ₂; apply ¬¬ₑ; refine Hnnp }
        { assume Hnq;  apply ∨ᵢ₁; refine Hnq }
    }
    {
        assume H; rewrite left imp_eq_or;
        have H1: π ((¬ q) ∨ p) { rewrite imp_eq_or; refine H };
        apply ∨ₑ H1
        { assume Hnq;  apply ∨ᵢ₂; refine Hnq }
        { assume Hp;  apply ∨ᵢ₁; rewrite not_simplify1; refine Hp }
    }
end;

opaque symbol implies_simplify2 p : π ((⊥ ⇒ p) = ⊤) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᵢ
    { assume H; apply ⊤ᵢ }
    { assume H; rewrite left imp_eq_or; apply ∨ᵢ₁; refine neg_⊥ }
end;

opaque symbol implies_simplify3 p : π ((p ⇒ ⊤) = ⊤) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᵢ
    { assume H; apply ⊤ᵢ }
    { assume H H2; apply ⊤ᵢ  }
end;

opaque symbol implies_simplify4 p : π ((⊤ ⇒ p) = p) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᵢ
    { 
        assume H;
        have H1: π ⊤ → π p {
            refine H
        };
        apply H1;
        apply ⊤ᵢ
    }
    { assume H H2; apply H }
end;

opaque symbol implies_simplify5 p : π ((p ⇒ ⊥) = ¬ p) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᵢ
    { 
        assume H;
        have H1: π p → π ⊥ {
            refine H
        };
        refine H1
    }
    { assume H H2; apply (fold_⇒ H) H2  }
end;

opaque symbol implies_simplify6 p : π ((p ⇒ p) = ⊤) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᵢ
    { 
        assume H;
        apply ⊤ᵢ
    }
    { assume H H2; apply H2  }
end;

opaque symbol implies_simplify7 p : π ((¬ p ⇒ p) = p) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left imp_eq_or;
    apply ∧ᵢ
    { 
        assume H;
        apply ∨ₑ H
        { assume Hnnp; apply ¬¬ₑ; refine Hnnp }
        { assume Hp; refine Hp }
    }
    { assume Hp; apply ∨ᵢ₂; apply Hp }
end;

opaque symbol implies_simplify8 p : π ((p ⇒ ¬ p) = ¬ p) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left imp_eq_or;
    apply ∧ᵢ
    { 
        assume H;
        apply ∨ₑ H
        { assume Hnp; refine Hnp }
        { assume Hnp; refine Hnp }
    }
    { assume Hnp; apply ∨ᵢ₂; refine Hnp }
end;

symbol all_implies_simplify ≔ 
    (#rewrite implies_simplify1) ⸬ (#rewrite implies_simplify2) ⸬ (#rewrite implies_simplify3)
    ⸬ (#rewrite implies_simplify4) ⸬(#rewrite implies_simplify5) ⸬ (#rewrite implies_simplify6) ⸬ (#rewrite implies_simplify7) ⸬  (#rewrite implies_simplify8) ⸬  □;

symbol implies_simplify ≔ #repeat (applyAny all_implies_simplify) and #try (#reflexivity #orelse (#apply ⊤ᵢ));



// Rule 74. ite_simplify
opaque symbol ite_simplify1 a (t1 t2: τ a) : π (ite ⊤ t1 t2 = t1) ≔
begin
    assume a t1 t2;
    refine ite_ind ⊤ t1 t2 (λ u, u = t1) _ _
    {assume h; reflexivity}
    {assume contra; refine ⊥ₑ (contra ⊤ᵢ)}
end;

opaque symbol ite_simplify2 a (t1 t2: τ a) : π (ite ⊥ t1 t2 = t2) ≔
begin
    assume a t1 t2;
    refine ite_ind ⊥ t1 t2 (λ u, u = t2) _ _
    {assume h; refine ⊥ₑ h }
    {assume h; reflexivity }
end;

opaque symbol ite_simplify3 c : π ((@ite o c ⊤ ⊤) = ⊤) ≔
begin
    assume c;
    refine ite_ind c ⊤ ⊤ (λ u, u = ⊤) _ _
    {reflexivity}
    {reflexivity}
end;

opaque symbol ite_simplify4 a c (t1 t2: τ a) : π ((ite (¬ c) t1 t2) = (ite c t2 t1)) ≔
begin
    assume a c t1 t2;
    refine ite_ind (¬ c) t1 t2 (λ u, u = (ite c t2 t1)) _ _
    {
        assume hnc;
        refine ite_ind (c) t2 t1 (λ u, t1 = u) _ _
        { assume hc; refine ⊥ₑ (hnc hc) }
        { assume h; reflexivity }
    }
    {
        assume hnnc;
        refine ite_ind (c) t2 t1 (λ u, t2 = u) _ _
        { assume hc; reflexivity }
        { assume h; refine ⊥ₑ (hnnc h) }
    }
end;

opaque symbol ite_then [a] c (t1 t2: τ a) : π c → π (t1 = ite c t1 t2) ≔
begin
    assume a c t1 t2;
    assume hc;
    refine ite_ind c t1 t2 (λ u, t1 = u) _ _
    {  reflexivity }
    { assume hnc;  refine ⊥ₑ (hnc hc) }
end;

opaque symbol ite_else [a] c (t1 t2: τ a) : π (¬ c) → π (t2 = ite c t1 t2) ≔
begin
    assume a c t1 t2;
    assume hnc;
    refine ite_ind c t1 t2 (λ u, t2 = u) _ _
    { assume hc;  refine ⊥ₑ (hnc hc) }
    {  reflexivity }
end;

opaque symbol ite_simplify5 a c (t1 t2 t3: τ a) : π (ite c (ite c t1 t2) t3 = ite c t1 t3) ≔
begin
    assume a c t1 t2 t3;
    refine ite_ind (c) (ite c t1 t2) t3 (λ u, u = ite c t1 t3) _ _
    {
        assume hc;
        rewrite left ite_then c t1 t2 hc;
        rewrite left ite_then c t1 t3 hc;
        reflexivity
    }
    {
        assume hnc;
        rewrite left ite_else c t1 t3 hnc;
        reflexivity
    }
end;

opaque symbol ite_simplify6 a c (t1 t2 t3: τ a) : π (ite c t1 (ite c t2 t3) = ite c t1 t3) ≔
begin
    assume a c t1 t2 t3;
    refine ite_ind c t1 (ite c t2 t3) (λ u, u = ite c t1 t3) _ _
    {
        assume hc;
        rewrite left ite_then c t1 t3 hc;
        reflexivity
    }
    {
        assume hnc;
        rewrite left ite_else c t1 t3 hnc;
        rewrite left ite_else c t2 t3 hnc;
        reflexivity
    }
end;

opaque symbol ite_simplify7 c : π (ite c ⊤ ⊥ = c) ≔
begin
    assume c;
    refine ite_ind c ⊤ ⊥ (λ u, u = c) _ _
    {
        assume hc;
        apply prop_ext;
        apply ∧ᵢ
        { simplify; assume h; refine hc }
        { assume hcc; apply ⊤ᵢ }
    }
    {
        assume hnc;
        apply prop_ext;
        apply ∧ᵢ
        { simplify; assume h; refine ⊥ₑ h }
        { assume hc; refine hnc hc }
    }
end;

opaque symbol ite_simplify8 c : π (ite c ⊥ ⊤ = ¬ c) ≔
begin
    assume c;
    refine ite_ind c ⊥ ⊤ (λ u, u = ¬ c) _ _
    {
        assume hc;
        apply prop_ext;
        apply ∧ᵢ
        { simplify; assume h; refine ⊥ₑ h }
        { simplify; assume hnc; refine hnc hc }
    }
    {
        assume hc;
        apply prop_ext;
        apply ∧ᵢ
        { simplify; assume h; refine hc }
        { assume hcc; apply ⊤ᵢ }
    }
end;

opaque symbol ite_simplify9 c t : π (ite c ⊤ t = (c ∨ t)) ≔
begin
    assume c t;
    refine ite_ind c ⊤ t (λ u, u = (c ∨ t)) _ _
    {
        assume hc;
        apply prop_ext;
        apply ∧ᵢ
        {assume h; apply ∨ᵢ₁; refine hc }
        {assume h; apply ⊤ᵢ}
    }
    {
        assume hnc;
        apply prop_ext;
        apply ∧ᵢ
        {assume h; apply ∨ᵢ₂; refine h }
        {assume h; apply ∨ₑ h { assume hc; refine ⊥ₑ (hnc hc) } { refine λ x, x }}
    }
end;

opaque symbol ite_simplify10 c t : π ((ite c t ⊥) = (c ∧ t)) ≔
begin
    assume c t;
    refine ite_ind c t ⊥ (λ u, u = (c ∧ t)) _ _
    {
        assume hc;
        apply prop_ext;
        apply ∧ᵢ
        { assume ht; apply ∧ᵢ { refine hc } { refine ht }  }
        { assume h; apply ∧ₑ₂ h }
    }
    {
        assume hc;
        apply prop_ext;
        apply ∧ᵢ
        { assume contra; refine ⊥ₑ contra }
        { assume h; refine hc _; refine ∧ₑ₁ h }
    }
end;

opaque symbol ite_simplify11 c t : π (ite c ⊥ t = ((¬ c) ∧ t)) ≔
begin
    assume c t;
    refine ite_ind c ⊥ t (λ u, u = ((¬ c) ∧ t)) _ _
    {
        assume hc;
        apply prop_ext;
        apply ∧ᵢ
        { assume hcontra; refine ⊥ₑ hcontra }
        { assume h; refine ∧ₑ₁ h _; refine hc }
    }
    {
        assume hnc;
        apply prop_ext;
        apply ∧ᵢ
        { assume ht; apply ∧ᵢ { refine hnc } { refine ht } }
        { assume h; refine ∧ₑ₂ h }
    }
end;

opaque symbol ite_simplify12 c t : π (ite c t ⊤ = ((¬ c) ∨ t)) ≔
begin
    assume c t;
    refine ite_ind c t ⊤ (λ u, u = ((¬ c) ∨ t)) _ _
    {
        assume hc;
        apply prop_ext;
        apply ∧ᵢ
        { assume ht; apply ∨ᵢ₂; refine ht }
        { assume h; apply ∨ₑ h { assume hnc; refine ⊥ₑ (hnc hc) } { refine λ x, x } }
    }
    {
        assume hnc;
        apply prop_ext;
        apply ∧ᵢ
        { assume h; apply ∨ᵢ₁; refine hnc }
        {
            assume h;
            apply ∨ₑ h
            { assume h2; apply ⊤ᵢ }
            { assume h2; apply ⊤ᵢ }
        }
    }
end;

symbol all_ite_simplify a ≔ 
    (#rewrite (ite_simplify1 a))
    ⸬ (#rewrite (ite_simplify2 a))
    ⸬ (#rewrite ite_simplify3)
    ⸬ (#rewrite (ite_simplify4 a)) 
    ⸬ (#rewrite (ite_simplify5 a)) 
    ⸬ (#rewrite (ite_simplify6 a)) 
    ⸬ (#rewrite ite_simplify7) 
    ⸬ (#rewrite ite_simplify8) 
    ⸬ (#rewrite ite_simplify9) 
    ⸬ (#rewrite ite_simplify10)
    ⸬ (#rewrite ite_simplify11)
    ⸬  (#rewrite ite_simplify12)
    ⸬ □;

symbol ite_simplify [a] ≔ #repeat (applyAny (all_ite_simplify a)) and #try (#reflexivity #orelse (#apply ⊤ᵢ));

// Rule 73: ac_simp
symbol ac_simp_and ≔ #repeat (#rewrite_gen "" " " ∧_assoc) and #repeat (#rewrite ∧_idem) and #reflexivity;
symbol ac_simp_or ≔ #repeat (#rewrite_gen "" " " ∨_assoc) and #repeat (#rewrite ∨_idem) and #reflexivity;

opaque symbol eq_symm [a] [x y: τ a] : π̇ (((x = y) = (y = x)) ⸬ □) ≔
begin
  assume a x y;
  apply ∨ᵢ₁;
  apply prop_ext;
  apply ∧ᵢ
  { assume H; symmetry; apply H }
  { assume H; symmetry; apply H }
end;

/* ------------------------------------------------------------------------
   cvc5 RARE Boolean rewrites (was alethe.Rare)
   ------------------------------------------------------------------------ */

opaque symbol eq-refl [a] (t: τ a) : π ((t = t) = ⊤) ≔ begin
    assume a p;
    apply prop_ext;
    apply ∧ᵢ
    { assume H; remove H; apply ⊤ᵢ  }
    { assume H⊤; remove H⊤; reflexivity } 
end;

// (define-rule eq-symm ((t ?) (s ?)) (= t s) (= s t))
opaque symbol eq-symm [a] (t s: τ a) : π ((t = s) = (s = t)) ≔
begin
    assume a t s;
    apply prop_ext;
    apply ∧ᵢ
    {
        assume H;
        symmetry; apply H
    }
    {
        assume H;
        symmetry; apply H
    }
end;

// (define-rule bool-impl-false1 ((t Bool)) (=> t false) (not t))
opaque symbol bool-impl-false1 t : π ((t ⇒ ⊥) = ¬ t) ≔ implies_simplify5 t;

// (define-rule bool-impl-false2 ((t Bool)) (=> false t) true)
opaque symbol bool-impl-false2 t : π ((⊥ ⇒ t) = ⊤) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    { assume Htbot; apply ⊤ᵢ  }
    { assume Htop;  assume Ht; apply ⊥ₑ Ht }
end;

// (define-rule bool-double-not-elim ((t Bool)) (not (not t)) t)
// Duplicate of Alethe
opaque symbol bool-double-not-elim t : π ((¬ (¬ t)) = t) ≔ not_simplify1 t;


//(define-rule bool-impl-elim ((t Bool) (s Bool)) (=> t s) (or (not t) s))
opaque symbol bool-impl-elim s t: π ((s ⇒ t) = ((¬ s) ∨ t)) ≔
begin
  assume s t;
  apply prop_ext;
  apply ∧ᵢ
  {  assume Himp; apply imply_to_or Himp }
  {  assume Hor; refine or_to_imply Hor }
end;

//(define-rule distinct-binary-elim ((t ?) (s ?)) (distinct t s) (not (= t s)))
opaque symbol distinct-binary-elim [a] (t s: τ a) : π (distinct (cons t (cons s ⧈)) = ( t ≠ s)) ≔ eq_refl (distinct (cons t (cons s ⧈)));

// (define-rule bool-impl-true2 ((t Bool)) (=> true t) t)
opaque symbol bool-impl-true2 t : π ((⊤ ⇒ t) = t) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    {   assume HTopt; apply HTopt ⊤ᵢ }
    {  assume Ht;  assume Htop; apply Ht }
end;

// (define-rule bool-impl-true1 ((t Bool)) (=> t true) true)
opaque symbol bool-impl-true1 t : π ((t ⇒ ⊤) = ⊤) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    {   assume HTopt; apply ⊤ᵢ }
    {  assume Ht;  assume Htop; apply ⊤ᵢ }
end;


// (define-rule* bool-and-true ((xs Bool :list) (ys Bool :list)) (and xs true ys) (and xs ys))
opaque symbol bool-and-true xs ys : π ((xs ∧ ⊤ ∧ ys) = (xs ∧ ys)) ≔
begin
    assume xs ys;
    rewrite ∧_com ⊤ ys;
    rewrite and_identity_r;
    reflexivity
end;

// (define-rule bool-and-false ((xs Bool :list) (ys Bool :list)) (and xs false ys) false)
opaque symbol bool-and-false xs ys : π ((xs ∧ ⊥ ∧ ys) = ⊥) ≔
begin
    assume xs ys;
    rewrite ∧_com ⊥ ys;
    rewrite and_domination;
    rewrite and_domination;
    reflexivity
end;

// (define-rule* bool-or-false ((xs Bool :list) (ys Bool :list)) (or xs false ys) (or xs ys))
opaque symbol bool-or-false xs ys : π ((xs ∨ ⊥ ∨ ys) = (xs ∨ ys)) ≔
begin
    assume xs ys; 
    rewrite ∨_com ⊥ ys;
    rewrite or_identity_r;
    reflexivity
end;

// (define-rule* bool-or-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list)) (or xs (or b ys) zs) (or xs b ys zs))
opaque symbol bool-or-flatten xs b ys zs : π ((xs ∨ (b ∨ ys) ∨ zs) = (xs ∨ b ∨ ys ∨ zs)) ≔
begin
    assume xs b ys zs;
    rewrite ∨_assoc;
    reflexivity
end;


// Reviewed bool-or-flatten without `xs`
// (define-rule* bool-or-flatten ((b Bool) (ys Bool :list) (zs Bool :list)) (or (or b ys) zs) (or b ys zs))
opaque symbol bool-or-flatten' b ys zs : π (((b ∨ ys) ∨ zs) = (b ∨ ys ∨ zs)) ≔
begin
    assume b ys zs;
    apply ∨_assoc;
end;

// (define-rule* bool-and-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list)) (and xs (and b ys) zs) (and xs b ys zs))
opaque symbol bool-and-flatten b [xs ys zs] : π ((xs ∧ (b ∧ ys) ∧ zs) = (xs ∧ b ∧ ys ∧ zs)) ≔
begin
    assume b xs ys zs;
    rewrite ∧_assoc;
    reflexivity
end;

// Reviewed bool-and-flatten without `xs`
// (define-rule* bool-and-flatten ((b Bool) (ys Bool :list) (zs Bool :list)) (and (and b ys) zs) (and b ys zs))
opaque symbol bool-and-flatten' b ys zs : π (((b ∧ ys) ∧ zs) = (b ∧ ys ∧ zs)) ≔
begin
    assume b ys zs;
    apply ∧_assoc;
end;

// (define-rule bool-eq-true ((t Bool)) (= t true) t)
opaque symbol bool-eq-true (t: τ o) : π ((t = ⊤) = t) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    {
        
        assume H;
        rewrite H;
        apply ⊤ᵢ
    }
    {
        
        assume Ht;
        apply prop_ext;
        apply ∧ᵢ
        {  assume Ht'; apply ⊤ᵢ }
        {  assume Ht';  apply Ht }
    }
end;

// (define-rule bool-eq-false ((t Bool)) (= t false) (not t))
opaque symbol bool-eq-false (t: τ o) : π ((t = ⊥) = ¬ t) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    {
        
        assume H;
        rewrite H;
        assume Hbot;
        apply Hbot
    }
    {
        
        assume Hnt;
        apply prop_ext;
        apply ∧ᵢ
        {   assume Ht; apply (¬ₑ Hnt Ht) }
        {  assume Ht';  apply (⊥ₑ Ht') }
    }
end;

// (define-rule* bool-and-de-morgan ((x Bool) (y Bool) (zs Bool :list)) 
//   (not (and x y zs))
//   (not (and y zs))
//   (or (not x) _))
opaque symbol bool-and-de-morgan (x y zs: τ o): π ((¬ (x ∧ y ∧ zs)) = ((¬ x) ∨ (¬ y) ∨ (¬ zs))) ≔
begin
    assume x y zs;
    apply prop_ext;
    apply ∧ᵢ
    { rewrite morgan1; rewrite morgan1;  assume H; refine H }
    { rewrite morgan1; rewrite morgan1;  assume H; refine H }
end;

// (define-rule* bool-or-de-morgan ((x Bool) (y Bool) (zs Bool :list)) 
//   (not (or x y zs))
//   (not (or y zs))
//   (and (not x) _))
opaque symbol bool-or-de-morgan (x y zs: τ o): π ((¬ (x ∨ y ∨ zs)) = ((¬ x) ∧ (¬ y) ∧ (¬ zs))) ≔
begin
    assume x y zs;
    apply prop_ext;
    apply ∧ᵢ
    { rewrite morgan2; rewrite morgan2;  assume H; refine H }
    { rewrite morgan2; rewrite morgan2;  assume H; refine H }
end;


// Integer
opaque symbol bool_implies_or_distrib (y1 y2 z: τ o) : π (((y1 ∨ y2) ⇒ z) = ((y1 ⇒ z) ∧ (y2 ⇒ z))) ≔
begin
    assume y1 y2 z;
    apply prop_ext;
    apply ∧ᵢ
    {
        assume H;
        apply ∧ᵢ
        { assume H1; refine H (∨ᵢ₁ H1) }
        { assume H2; refine H (∨ᵢ₂ H2) }
    }
    {
        assume H H1;
        apply ∨ₑ H1
        { assume H2; refine (∧ₑ₁ H) H2 }
        { assume Hy; refine (∧ₑ₂ H) Hy }
    }
end;

//  (define-rule* bool-implies-or-distrib
//  ((y1 Bool) (y2 Bool) (ys Bool :list) (z Bool))
//      (=> (or y1 y2 ys) z)
//      (=> (or y2 ys) z)
//      (and (=> y1 z) _))
// Version with list of disjuncts `ys`
opaque symbol bool_implies_or_distrib_rec (y1 y2 ys z: τ o) : π (((y1 ∨ y2 ∨ ys) ⇒ z) = ((y1 ⇒ z) ∧ (y2 ∨ ys ⇒ z))) ≔
begin
    assume y1 y2 ys z;
    refine bool_implies_or_distrib y1 (y2 ∨ ys) z;
end;

// //FIXME: Move to Lia.lp ?
// la_disequality: 𝑡1 ≈ 𝑡2 ∨ ¬(𝑡1 ≤ 𝑡2) ∨ ¬(𝑡2 ≤ 𝑡1 )
opaque symbol ite-eq (c: τ o) [a] (x y: τ a) : π ((ite c ((ite c x y) = x) ((ite c x y) = y)) = ⊤) ≔
begin
  assume c a x y;
  apply prop_ext;
  apply ∧ᵢ
  { assume H; apply ⊤ᵢ }
  { assume Htop;
    refine ite_ind c ((ite c x y) = x) ((ite c x y) = y) (λ u, u) _ _
    { assume hc;
      refine ite_ind c x y (λ u, u = x) _ _
      { assume hc2; reflexivity }
      { assume hnc; refine ⊥ₑ (hnc hc) } }
    { assume hnc;
      refine ite_ind c x y (λ u, u = y) _ _
      { assume hc; refine ⊥ₑ (hnc hc) }
      { assume hc2; reflexivity } } }
end;

