// cvc5 RARE arith-* rewrites over the reals
require open alethe.real Stdlib.PropExt;

// (define-rule arith-elim-lt ((t ?) (s ?)) (< t s) (not (>= t s)))
opaque symbol arith-elim-lt (t s : τ real) : π ((t <ᵣ s) = ¬ (t ≥ᵣ s)) ≔
begin
  assume t s; reflexivity
end;

// (define-rule arith-geq-norm2 ((t ?) (s ?)) (>= t s) (<= (- t) (- s)))
opaque symbol arith-geq-norm2 (t s : τ real) : π ((t ≥ᵣ s) = (—ᵣ t ≤ᵣ —ᵣ s)) ≔
begin
  assume t s;
  refine propExt _ _ (opp_le s t) _;
  assume h; rewrite left opp_opp t; rewrite left opp_opp s;
  refine opp_le (—ᵣ t) (—ᵣ s) h
end;

// (define-rule arith-geq-norm1 ((t ?) (s ?)) (>= t s) (>= (- t s) 0))
opaque symbol arith-geq-norm1 (t s : τ real) : π ((t ≥ᵣ s) = ((t −ᵣ s) ≥ᵣ zero)) ≔
begin
  assume t s; refine propExt _ _ (sub_nonneg_of_le s t) (le_of_sub_nonneg s t)
end;

// (define-rule arith-elim-gt ((t ?) (s ?)) (> t s) (not (<= t s)))
opaque symbol arith-elim-gt (t s : τ real) : π ((t >ᵣ s) = ¬ (t ≤ᵣ s)) ≔
begin
  assume t s; reflexivity
end;

// (define-rule arith-elim-leq ((t ?) (s ?)) (<= t s) (>= s t))
opaque symbol arith-elim-leq (t s : τ real) : π ((t ≤ᵣ s) = (s ≥ᵣ t)) ≔
begin
  assume t s; reflexivity
end;

// (define-rule arith-refl-leq ((t ?)) (<= t t) true)
opaque symbol arith-refl-leq (t : τ real) : π ((t ≤ᵣ t) = ⊤) ≔
begin
  assume t; refine propExt _ _ (λ _, ⊤ᵢ) (λ _, le_refl t)
end;

// (define-rule arith-refl-lt ((t ?)) (< t t) false)
opaque symbol arith-refl-lt (t : τ real) : π ((t <ᵣ t) = ⊥) ≔
begin
  assume t; refine propExt _ _ (λ h, h (le_refl t)) (λ h, ⊥ₑ h)
end;

// (define-rule arith-refl-geq ((t ?)) (>= t t) true)
opaque symbol arith-refl-geq (t : τ real) : π ((t ≥ᵣ t) = ⊤) ≔
begin
  assume t; refine propExt _ _ (λ _, ⊤ᵢ) (λ _, le_refl t)
end;

// (define-rule arith-refl-gt ((t ?)) (> t t) false)
opaque symbol arith-refl-gt (t : τ real) : π ((t >ᵣ t) = ⊥) ≔
begin
  assume t; refine propExt _ _ (λ h, h (le_refl t)) (λ h, ⊥ₑ h)
end;

// (define-rule arith-real-eq-elim ((t Real) (s Real)) (= t s) (and (>= t s) (<= t s)))
opaque symbol arith-real-eq-elim (t s : τ real) : π ((t = s) = ((t ≥ᵣ s) ∧ (t ≤ᵣ s))) ≔
begin
  assume t s;
  refine propExt _ _ _ _
  { assume h; rewrite h; refine ∧ᵢ (le_refl s) (le_refl s) }
  { assume h; refine le_antisymmetric t s (∧ₑ₂ h) (∧ₑ₁ h) }
end;
