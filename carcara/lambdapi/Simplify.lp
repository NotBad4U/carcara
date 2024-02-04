require open Stdlib.Prop;
require open Stdlib.FOL;
require open Stdlib.Set;
require open Stdlib.Eq;
require open lambdapi.Alethe;

notation ¬ prefix 8;

// Use it to unfold the definition of `¬`.
// The tactic simplify is to agressive.
opaque symbol negdef p : π ((p ⇒ ⊥) = ¬ p) ≔
begin
    simplify;
    reflexivity
end;

// Rule 71: equiv_simplify

symbol equiv_simplify₁ p q : π (((¬ p) = ¬ q) = (p = q)) ≔
begin
    assume p q;
    apply prop_ext;
    apply ∧ᶜᵢ
    {
        apply ⟹ᶜᵢ;
        assume Heq;
        apply prop_ext; 
        apply ∧ᶜᵢ
        {
            rewrite left imp_eq_or;
            rewrite Heq;
            rewrite or_com;
            apply classic
        }
        {
            rewrite left imp_eq_or;
            rewrite left Heq;
            rewrite or_com;
            apply classic
        }
    }
    {
        apply ⟹ᶜᵢ;
        assume Heq;
        rewrite Heq;
        reflexivity
    }
end;

symbol equiv_simplify₂ p : π ((p = p) = ⊤) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᶜᵢ
    { apply ⟹ᶜᵢ; assume H; remove H; apply trivial }
    { apply ⟹ᶜᵢ; assume H⊤; remove H⊤; reflexivity }
end;

symbol equiv_simplify₃ p : π ((p = (¬ p)) = ⊥) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left iff_equiv_eq;
    simplify;
    rewrite left imp_eq_or;
    rewrite left imp_eq_or;
    rewrite left imp_eq_or;
    rewrite left imp_eq_or;
    apply ∧ᶜᵢ
    {
        rewrite or_identity;
        rewrite morgan₁;
        rewrite .[¬ ((¬ (p ⇒ ⊥)) ∨ᶜ p)] morgan₂;
        rewrite distributive_or;
        rewrite negdef;
        rewrite or_idempotent;
        apply ∧ᶜᵢ
        {
            apply classic
        }
        {
            rewrite or_com;
            apply classic
        };
    }
    {
        rewrite negdef;
        apply ∨ᶜᵢ₁;
        refine neg_true
    }
end;

symbol equiv_simplify₄ p : π ((p = ⊤) = p) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left iff_equiv_eq;
    apply ∧ᶜᵢ
    {
        apply ⟹ᶜᵢ;
        assume H;
        apply ⟺ᶜₑ H;
        assume H1 H2;
        apply H2;
        apply trivial
    }
    {
        apply ⟹ᶜᵢ;
        assume Hp;
        apply ∧ᶜᵢ
        { apply ⟹ᶜᵢ; assume Hp'; apply trivial }
        { apply ⟹ᶜᵢ; assume Htop; apply Hp }
    }
end;

symbol equiv_simplify₅ p : π ((p = ⊥) = ¬ p) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left iff_equiv_eq;
    apply ∧ᶜᵢ
    {
        apply ⟹ᶜᵢ;
        assume H;
        apply ⟺ᶜₑ H;
        assume H1 H2;
        admit
    }
    {
        apply ⟹ᶜᵢ;
        assume Hnp;
        apply ∧ᶜᵢ
        {
            apply ⟹ᶜᵢ;
            assume Hp;
            admit
        }
        {
            apply ⟹ᶜᵢ;
            assume Hbot; 
            apply ⊥ₑ;
            apply Hbot
        }
    }
end;

symbol equiv_simplify₆ p : π ((⊥ = p) = ¬ p) ≔
begin
    assume p;
    admit //FIXME: need sym
end;

// (define-rule bool-impl-false1 ((t Bool)) (=> t false) (not t))
opaque symbol bool-impl-false1 t : π ((t ⟹ᶜ ⊥) = ¬ t) ≔
begin
    assume t;
    rewrite left imp_eq_or;
    apply prop_ext;
    apply ∧ᶜᵢ
    {
        apply ⟹ᶜᵢ;
        assume H;
        apply ∨ᶜₑ H
        { assume Hnt; refine Hnt; }
        { assume Hbot; apply ⊥ₑ; apply Hbot }
    }
    {
        apply ⟹ᶜᵢ;
        assume Hnt;
        apply ∨ᶜᵢ₁;
        refine Hnt;
    }
end;

// (define-rule bool-double-not-elim ((t Bool)) (not (not t)) t)
opaque symbol bool-double-not-elim t : π ((¬ (¬ t)) = t) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᶜᵢ
    {
        rewrite nnpp_eq;
        apply ⟹ᶜᵢ;
        assume Ht;
        apply Ht
    }
    {
        rewrite nnpp_eq;
        apply ⟹ᶜᵢ;
        assume Ht;
        apply Ht
    }
end;

// Rule 69: not_simplify

opaque symbol not_simplify₁ p : π ((¬ (¬ p)) = p) ≔ bool-double-not-elim p;

opaque symbol not_simplify₂ : π ((¬ ⊥) = ⊤) ≔
begin
    simplify;
    apply prop_ext;
    apply ∧ᶜᵢ
    { apply ⟹ᶜᵢ; assume H; apply trivial }
    { apply ⟹ᶜᵢ; assume Htop Hbot; refine Hbot }
end;

opaque symbol not_simplify₃ : π ((¬ ⊤) = ⊥) ≔
begin
    simplify;
    apply prop_ext;
    apply ∧ᶜᵢ
    { apply ⟹ᶜᵢ; assume H; apply H; apply trivial }
    { apply ⟹ᶜᵢ; assume Hbot Htop; refine Hbot }
end;

// Rule 70: implies_simplify

opaque symbol implies_simplify₁ p q : π (( (¬ p) ⟹ᶜ (¬ q)) = (q ⟹ᶜ p)) ≔
begin
    assume p q;
    apply prop_ext;
    apply ∧ᶜᵢ
    { 
        apply  ⟹ᶜᵢ; assume H; rewrite left imp_eq_or;
        have H1: π ((¬ ¬ p) ∨ᶜ ¬ q) { rewrite imp_eq_or; refine H };
        apply ∨ᶜₑ H1
        { assume Hnnp;  apply ∨ᶜᵢ₂; apply nnpp; refine Hnnp }
        { assume Hnq;  apply ∨ᶜᵢ₁; refine Hnq }
    }
    {
        apply  ⟹ᶜᵢ; assume H; rewrite left imp_eq_or;
        have H1: π ((¬ q) ∨ᶜ p) { rewrite imp_eq_or; refine H };
        apply ∨ᶜₑ H1
        { assume Hnq;  apply ∨ᶜᵢ₂; refine Hnq }
        { assume Hp;  apply ∨ᶜᵢ₁; rewrite not_simplify₁; refine Hp }
    }
end;

opaque symbol implies_simplify₂ p : π ((⊥ ⟹ᶜ p) = ⊤) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᶜᵢ
    { apply ⟹ᶜᵢ; assume H; apply trivial }
    { apply ⟹ᶜᵢ; assume H; rewrite left imp_eq_or; apply ∨ᶜᵢ₁; refine neg_true  }
end;

opaque symbol implies_simplify₃ p : π ((p ⟹ᶜ ⊤) = ⊤) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᶜᵢ
    { apply ⟹ᶜᵢ; assume H; apply trivial }
    { apply ⟹ᶜᵢ; assume H; apply ⟹ᶜᵢ; assume H2; apply trivial  }
end;

opaque symbol implies_simplify₄ p : π ((⊤ ⟹ᶜ p) = p) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᶜᵢ
    { 
        apply ⟹ᶜᵢ; assume H;
        have H1: π ⊤ → π p {
            refine ⟹ᶜₑ H
        };
        apply H1;
        apply trivial
    }
    { apply ⟹ᶜᵢ; assume H; apply ⟹ᶜᵢ; assume H2; apply H }
end;

opaque symbol implies_simplify₅ p : π ((p ⟹ᶜ ⊥) = ¬ p) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᶜᵢ
    { 
        apply ⟹ᶜᵢ; assume H;
        have H1: π p → π ⊥ {
            refine ⟹ᶜₑ H
        };
        refine H1
    }
    { apply ⟹ᶜᵢ; assume H; apply ⟹ᶜᵢ; assume H2; apply H H2  }
end;

opaque symbol implies_simplify₆ p : π ((p ⟹ᶜ p) = ⊤) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᶜᵢ
    { 
        apply ⟹ᶜᵢ; assume H;
        apply trivial
    }
    { apply ⟹ᶜᵢ; assume H; apply ⟹ᶜᵢ; assume H2; apply H2  }
end;

opaque symbol implies_simplify₇ p : π (((¬ p) ⟹ᶜ p) = p) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left imp_eq_or;
    apply ∧ᶜᵢ
    { 
        apply ⟹ᶜᵢ; assume H;
        apply ∨ᶜₑ H
        { assume Hnnp; apply nnpp; refine Hnnp }
        { assume Hp; refine Hp }
    }
    { apply ⟹ᶜᵢ; assume Hp; apply ∨ᶜᵢ₂; apply Hp }
end;

opaque symbol implies_simplify₈ p : π ((p ⟹ᶜ ¬ p) = ¬ p) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left imp_eq_or;
    apply ∧ᶜᵢ
    { 
        apply ⟹ᶜᵢ; assume H;
        apply ∨ᶜₑ H
        { assume Hnp; refine Hnp }
        { assume Hnp; refine Hnp }
    }
    { apply ⟹ᶜᵢ; assume Hnp; apply ∨ᶜᵢ₂; refine Hnp }
end;


// Rule 74. ite_simplify
opaque symbol ite_simplify₁ t1 t2 : π (ite ⊤ t1 t2) ≔
begin
    assume t1 t2;
    simplify;
    rewrite left imp_eq_or;
    rewrite left imp_eq_or;
    rewrite negdef;
    rewrite distributive_and;
    apply ∨ᶜᵢ₁;
    rewrite and_com;
    rewrite distributive_and;
    apply ∨ᶜᵢ₁;
    rewrite left morgan₂;
    assume H;
    apply ∨ᶜₑ H
    { assume Hntop; apply Hntop; apply trivial  }
    { admit }
end;