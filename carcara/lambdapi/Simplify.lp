require open Stdlib.Prop;
require open Stdlib.FOL;
require open Stdlib.Set;
require open Stdlib.Nat;
require open Stdlib.Eq;
require open Stdlib.Bool;
require open Stdlib.List;
require open lambdapi.Alethe;

symbol equiv_simplify₁ p q : π (((¬ᶜ p) = ¬ᶜ q) = (p = q)) ≔
begin
    assume p q;
    apply prop_ext;
    apply ⟺ᶜᵢ
    {
        assume Heq;
        apply prop_ext;
        rewrite iff_def;
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
        assume Heq;
        rewrite Heq;
        reflexivity
    }
end;

symbol equiv_simplify₂ p : π ((p = p) = ⊤) ≔
begin
    assume p;
    apply prop_ext;
    apply ⟺ᶜᵢ
    { assume H; remove H; apply trivial }
    { assume H⊤; remove H⊤; reflexivity }
end;

symbol equiv_simplify₃ p : π ((p = (¬ᶜ p)) = ⊥) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left iff_equiv_eq;
    rewrite iff_def; 
    rewrite iff_def;
    rewrite left imp_eq_or;
    rewrite left imp_eq_or;
    rewrite left imp_eq_or;
    rewrite left imp_eq_or;
    apply ∧ᶜᵢ
    {
        rewrite ∨ᶜ_idempotence;
        rewrite morgan;
        apply ∨ᶜᵢ₂;
        rewrite or_com;
        apply and_not_or; 
        rewrite morgan;
        rewrite nnpp_eq;
        apply classic
    }
    {
        apply ∨ᶜᵢ₂;
        rewrite or_idem;
        rewrite distributive_and;
        rewrite distributive_or;
        apply ∧ᶜᵢ
        {
            rewrite left nor;
            apply ∨ᶜᵢ₁;
            apply classic
        }
        {
            rewrite left nor;
            apply ∨ᶜᵢ₁;
            apply classic
        }
    }
end;

symbol equiv_simplify₄ p : π ((p = ⊤) = p) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left iff_equiv_eq;
    apply ⟺ᶜᵢ
    {
        assume H;
        apply ⟺ᶜₑ H;
        assume H1 H2;
        apply H2;
        apply trivial
    }
    {
        assume Hp;
        apply ⟺ᶜᵢ
        { assume Hp'; apply trivial }
        { assume Htop; apply Hp }
    }
end;

symbol equiv_simplify₅ p : π ((p = ⊥) = ¬ᶜ p) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left iff_equiv_eq;
    apply ⟺ᶜᵢ
    {
        assume H;
        apply ⟺ᶜₑ H;
        assume H1 H2;
        admit
    }
    {
        assume Hnp;
        apply ⟺ᶜᵢ
        {
            assume Hp;
            admit
        }
        {
            assume Hbot; 
            apply ⊥ₑ;
            apply Hbot
        }
    }
end;

// (define-rule bool-impl-false1 ((t Bool)) (=> t false) (not t))
symbol bool-impl-false1 t : π ((t ⟹ᶜ ⊥) = ¬ᶜ t) ≔
begin
    assume t;
    rewrite left imp_eq_or;
    apply prop_ext;
    apply ⟺ᶜᵢ
    {
        assume H;
        apply ∨ᶜₑ H
        { assume Hnt; apply Hnt; }
        { assume Hbot; apply ⊥ₑ; apply Hbot }
    }
    {
        assume Hnt;
        apply ∨ᶜᵢ₁;
        apply Hnt;
    }
end;

// (define-rule bool-double-not-elim ((t Bool)) (not (not t)) t)
symbol bool-double-not-elim t : π ((¬ᶜ ¬ᶜ t) = t) ≔
begin
    assume t;
    apply prop_ext;
    rewrite iff_def;
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
