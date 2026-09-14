// cvc5 RARE arith-* rewrites over ℤ. A `rare_rewrite` step cites a lemma here by
// the RARE rule's name, so each lemma keeps that name verbatim. Opened with
// alethe.lia.
require open alethe.core alethe.lia;
require open Stdlib.Bool Stdlib.Comp Stdlib.Pos;

// core pins the decimal notation to ℕ and Stdlib.Pos pins it to ℙ; the last
// one loaded wins. These lemmas are about ℤ, so pin it back.
builtin "0" ≔ Stdlib.Z.Z0;
builtin "1" ≔ Stdlib.Z._1;
builtin "2" ≔ Stdlib.Z._2;
builtin "3" ≔ Stdlib.Z._3;
builtin "4" ≔ Stdlib.Z._4;
builtin "5" ≔ Stdlib.Z._5;
builtin "6" ≔ Stdlib.Z._6;
builtin "7" ≔ Stdlib.Z._7;
builtin "8" ≔ Stdlib.Z._8;
builtin "9" ≔ Stdlib.Z._9;
builtin "10" ≔ Stdlib.Z._10;

// (define-rule arith-elim-lt ((t ?) (s ?)) (< t s) (not (>= t s)))
opaque symbol arith-elim-lt t s : π ((t < s) = ¬ (t ≥ s)) ≔
begin
    assume t s;
    simplify;
    apply prop_ext;
    apply ∧ᵢ
    {
        assume H;
        assume H2;
        apply fold_⇒ H2;
        apply H  
    }
    {
        assume H;
        have H2: π (¬ ¬ istrue (isLt (t ≐ s))) { refine H };
        rewrite left nnpp_eq;
        refine H2
    }
end;

// (define-rule arith-geq-tighten ((t Int) (s Int)) (not (>= t s)) (>= s (+ t 1)))
opaque symbol arith-geq-tighten t s : π ((¬ (t ≥ s)) = (s ≥ (t + 1))) ≔
begin
admitted;

// (define-rule arith-geq-norm2 ((t ?) (s ?)) (>= t s) (<= (- t) (- s)))
opaque symbol arith-geq-norm2 t s : π ((t ≥ s) =  (— t ≤ — s)) ≔
begin 
    assume t s;
    apply prop_ext;
    apply ∧ᵢ
    {
        refine (∧ₑ₁ (opp_le_mono t s));
    }
    {
        refine (∧ₑ₂ (opp_le_mono t s));
    }
end;

// (define-rule arith-geq-norm1 ((t ?) (s ?)) (>= t s) (>= (- t s) 0))
opaque symbol arith-geq-norm1 t s : π ((t ≥ s) = ((t - s) ≥ 0)) ≔
begin 
    assume t s;
    apply prop_ext;
    apply ∧ᵢ
    {
        refine ge_implies_diff_nonneg t s;
    }
    {
        refine diff_nonneg_implies_ge t s;
    }
end;

// (define-rule arith-leq-norm ((t Int) (s Int)) (<= t s) (not (>= t (+ s 1))))
opaque symbol arith-leq-norm (t s: τ int) : π ((t ≤ s) = ¬ (t ≥ s + 1)) ≔
begin
    assume t s;
    apply prop_ext;
    apply ∧ᵢ
    {
        refine ≤-norm t s
    }
    {
        admit //TODO: prove me
    }
end;

// (define-rule arith-elim-gt ((t ?) (s ?)) (> t s) (not (<= t s)))
opaque symbol arith-elim-gt (t s: τ int) : π ((t > s) = (¬ (t ≤ s))) ≔
begin 
assume t s;
apply prop_ext;
apply ∧ᵢ
{
    refine >_neg_≤ t s
}
{
    refine (λ x, x);
}
end;

// (define-rule arith-elim-leq ((t ?) (s ?)) (<= t s) (>= s t))
opaque symbol arith-elim-leq (t s: τ int) : π ((t ≤ s) = (s ≥ t)) ≔
begin 
    assume t s;
    apply prop_ext;
    apply ∧ᵢ
    {
        assume H;
        refine (∧ₑ₂ (≤_≥ s t)) H
    }
    {
        assume H;
        refine (∧ₑ₁ (≤_≥ s t)) H
    }
end;

// (define-rule arith-refl-leq ((t ?)) (<= t t) true)
opaque symbol arith-refl-leq (t: τ int) : π ((t ≤ t) = ⊤) ≔
begin
assume t;
apply prop_ext;
apply ∧ᵢ
{  assume H; apply ⊤ᵢ }
{
     assume Htop;
    refine (≤_refl t)
}
end;

// (define-rule arith-refl-lt ((t ?)) (< t t) false)
opaque symbol arith-refl-lt (t: τ int) : π ((t < t) = ⊥) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    {
        refine <_no_refl t
    }
    {
        
        assume Hbot;
        apply ⊥ₑ Hbot 
    }
end;

// (define-rule arith-refl-geq ((t ?)) (>= t t) true)
opaque symbol arith-refl-geq (t: τ int) : π ((t ≥ t) = ⊤) ≔
begin
assume t;
apply prop_ext;
apply ∧ᵢ
{  assume H; apply ⊤ᵢ }
{
     assume Htop;
    refine (≥_refl t)
}
end;

// (define-rule arith-refl-gt ((t ?)) (> t t) false)
opaque symbol arith-refl-gt (t: τ int) : π ((t > t) = ⊥) ≔
begin 
assume t;
apply prop_ext;
apply ∧ᵢ
{
    generalize t;
    assume t;
    refine >_no_refl t;
}
{
    
    assume Hbot;
    apply ⊥ₑ Hbot 
};
end;

// (define-rule arith-int-eq-elim ((t Int) (s Int)) (= t s) (and (>= t s) (<= t s)))
opaque symbol arith-int-eq-elim (t s: τ int) : π ((t = s) = ((t ≥ s) ∧ (t ≤ s))) ≔
begin
assume t s;
apply prop_ext;
apply ∧ᵢ
{
     assume Heq;
    rewrite Heq;
    apply ∧ᵢ 
    {
        refine (≥_refl s)
    }
    {
        refine (≤_refl s)
    }
}
{
    assume H1;
    refine  ≤_antisym t s _ _
    {
        refine (∧ₑ₁ (≤_≥ s t)) _;
        refine (∧ₑ₂ (≤_≥ s t)) (∧ₑ₂ H1);
    }
    {  refine  (∧ₑ₁ (≤_≥ t s)) (∧ₑ₁ H1); }
}
end;
