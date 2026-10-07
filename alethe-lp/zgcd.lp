// All definitions inspired by https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.PArith.BinPosDef.html

require open Stdlib.Nat Stdlib.Z Stdlib.Prop Stdlib.Prod;
// For its global rules (`add H $y ↪ succ $y`, …), which the proofs below
// compute with; not opened, since it opens Stdlib.Z's `+` over ℕ's.
require Stdlib.ExtraRules;


inductive Mask: TYPE ≔
| IsNul : Mask
| IsPos : ℙ →  Mask
| IsNeg : Mask
;

symbol mask: Set;
rule τ mask ↪ Mask;

symbol sub': Mask → ℙ;
rule sub' (IsPos $p) ↪ $p
with sub' IsNeg ↪ H
with sub' IsNul ↪ H
;

// x -> 2*x
symbol double_mask: Mask → Mask;
rule double_mask IsNul ↪ IsNul
with double_mask IsNeg ↪ IsNeg
with double_mask (IsPos $x) ↪ IsPos (O $x)
;

// x -> 2*x-1
symbol pred_double : ℙ → ℙ;
rule pred_double (I $x) ↪ I (O $x)
with pred_double (O $x) ↪ I (pred_double $x)
with pred_double H ↪ H
;

compute val ((O (O (I H))));
compute val (pred_double (O (O (I H))));

//  x -> 2*x - 2
symbol double_pred_mask: ℙ → Mask;
rule double_pred_mask H ↪ IsNul
with double_pred_mask (I $x) ↪ IsPos (O (O $x))
with double_pred_mask (O $x) ↪ IsPos (O (pred_double $x))
;

// x -> 2 * x + 1
symbol suc_double_mask: Mask → Mask;
rule suc_double_mask IsNul ↪ IsPos H
with suc_double_mask IsNeg ↪ IsNeg
with suc_double_mask (IsPos $x) ↪ IsPos (I $x)
;

symbol sub_mask_carry :  ℙ → ℙ → Mask;
symbol sub_mask :  ℙ → ℙ → Mask;

rule sub_mask_carry (I $p) (I $q) ↪ suc_double_mask (sub_mask_carry $p $q)
with sub_mask_carry (I $p) (O $q) ↪ double_mask (sub_mask $p $q)
with sub_mask_carry (I $p) H ↪ IsPos (pred_double $p)
with sub_mask_carry (O $p) (I $q) ↪ double_mask (sub_mask_carry $p $q)
with sub_mask_carry (O $p) (O $q) ↪ suc_double_mask (sub_mask_carry $p $q)
with sub_mask_carry (O $p) H ↪ double_pred_mask $p
with sub_mask_carry H _ ↪ IsNeg
;

rule sub_mask (I $p) (I $q) ↪ double_mask (sub_mask $p $q)
with sub_mask (I $p) (O $q) ↪ suc_double_mask (sub_mask $p $q)
with sub_mask (I $p) H ↪ IsPos (O $p)
with sub_mask (O $p) (I $q) ↪ suc_double_mask (sub_mask_carry $p $q)
with sub_mask (O $p) (O $q) ↪ double_mask (sub_mask $p $q)
with sub_mask (O $p) H ↪ IsPos (pred_double $p)
with sub_mask H H ↪ IsNul
with sub_mask H (I $q) ↪ IsNeg
with sub_mask H (O $q) ↪ IsNeg
;

symbol sub: ℙ → ℙ → ℙ;
rule sub $a $b ↪ sub' (sub_mask $a $b);

// https://coq.inria.fr/doc/V8.18.0/aclia/Coq.PArith.BinPosDef.html#Pos.gcdn
symbol Stein_gcd (a b: ℙ): ℙ;
rule Stein_gcd H _ ↪ H    // 1 / gcd(1, b) = 1
with Stein_gcd _ H ↪ H    // gcd(a, 1) = 1
with Stein_gcd (O $a) (O $b) ↪ O (Stein_gcd $a $b) // gcd(2a, 2b) = 2 * gcd(a,b) bc 2 is a common divisor
with Stein_gcd (I $a) (O $b) ↪ (Stein_gcd $a $b) // u is odd then 2 is not a common division
with Stein_gcd (O $a) (I $b) ↪ (Stein_gcd $a (I $b))
with Stein_gcd (I $a) (I $b) ↪
    let res ≔ (compare $a $b) in
        if (isEq res) 
            (I $a)  // Eq
            (if (isLt res)
                (Stein_gcd (sub $b $a) (I $a)) // Lt
                (Stein_gcd (sub $a $b) (I $b))) // Gt
;

symbol abs: ℤ → ℤ;
rule abs Z0 ↪ Z0
with abs (Zpos $x) ↪ Zpos $x
with abs (Zneg $x) ↪ Zpos $x
;

// ============================================================
// Coq-style safe wrapper (mirrors Pos.gcd = gcdn (size_nat a + size_nat b) a b).
//
// Coq's Pos.gcdn returns the gcd given enough fuel; the public Pos.gcd
// passes `size_nat a + size_nat b` (sum of bit-lengths) as the fuel,
// which is provably sufficient. We mirror that pattern:
//   - size_nat          : bit-length of a positive.
//   - ggcd_fuel         : the bounded-fuel computation, mirroring Pos.ggcdn.
//   - ggcd_safe         : ggcd_fuel (size_nat x + size_nat y) x y.
//   - red_by_Stein_v2   : a/gcd projection of ggcd_safe.
//
// Correctness flows through ggcd_fuel_correct + ggcd_fuel_sym to give
// the cross identity red_by_Stein_v2_cross, which Z_red_Stein_correct
// consumes (Z_red_Stein and its correctness are defined at the end of
// this file, after all the supporting lemmas).

// Bit-length of a positive (Coq's Pos.size_nat).
symbol size_nat : ℙ → ℕ;
rule size_nat H ↪ _0 +1
with size_nat (O $p) ↪ size_nat $p +1
with size_nat (I $p) ↪ size_nat $p +1;

// ============================================================
// Coq's ggcdn — returns (gcd, (a/gcd, b/gcd)) as a triple.
// Mirrors Pos.ggcdn faithfully. In case (I a, I b) the recursion
// SWAPS arguments (first arg becomes sub b a / sub a b, second becomes
// I a / I b) — this is what makes the recursion terminate, unlike the
// original red_by_Stein where (9, 3) loops because the first arg is
// never reduced.
symbol ggcd_fuel : ℕ → ℙ → ℙ → τ (pos × pos × pos);
symbol ggcd_step_II : ℕ → ℙ → ℙ → Comp → τ (pos × pos × pos);

rule ggcd_fuel _0 $a $b ↪ H ‚ $a ‚ $b
with ggcd_fuel (_ +1) H $b ↪ H ‚ H ‚ $b
with ggcd_fuel (_ +1) $a H ↪ H ‚ $a ‚ H
with ggcd_fuel ($n +1) (O $a) (O $b) ↪
  let r ≔ ggcd_fuel $n $a $b in
    O ((r)₁) ‚ ((r)₂)
with ggcd_fuel ($n +1) (I $a) (O $b) ↪
  let r ≔ ggcd_fuel $n (I $a) $b in
    ((r)₁) ‚ (((r)₂)₁) ‚ O (((r)₂)₂)
with ggcd_fuel ($n +1) (O $a) (I $b) ↪
  let r ≔ ggcd_fuel $n $a (I $b) in
    ((r)₁) ‚ O (((r)₂)₁) ‚ (((r)₂)₂)
with ggcd_fuel ($n +1) (I $a) (I $b) ↪
  ggcd_step_II $n $a $b (compare $a $b)
;

rule ggcd_step_II _ $a _ Eq ↪ (I $a) ‚ H ‚ H
with ggcd_step_II $n $a $b Lt ↪
  let r ≔ ggcd_fuel $n (sub $b $a) (I $a) in
    ((r)₁) ‚ (((r)₂)₂) ‚ add (((r)₂)₂) (O (((r)₂)₁))
with ggcd_step_II $n $a $b Gt ↪
  let r ≔ ggcd_fuel $n (sub $a $b) (I $b) in
    ((r)₁) ‚ add (((r)₂)₂) (O (((r)₂)₁)) ‚ (((r)₂)₂)
;

// Safe wrappers at size_nat fuel.
symbol ggcd_safe : ℙ → ℙ → τ (pos × pos × pos);
rule ggcd_safe $x $y ↪
  ggcd_fuel (Stdlib.Nat.+ (size_nat $x) (size_nat $y)) $x $y;

// New a/gcd function, derived from ggcd_safe. Mirrors Coq's pattern.
symbol red_by_Stein_v2 : ℙ → ℙ → ℙ;
rule red_by_Stein_v2 $x $y ↪ ((ggcd_safe $x $y)₂)₁;

// Sanity checks: verify the v2 function on the problematic input (9, 3)
// where the old red_by_Stein loops.
assert ⊢ red_by_Stein_v2 (I H) (I (O (O H))) ≡ H;            // 3, 9 → 1
assert ⊢ red_by_Stein_v2 (I (O (O H))) (I H) ≡ I H;          // 9, 3 → 3
assert ⊢ mul (red_by_Stein_v2 (I H) (I (O (O H)))) (I (O (O H)))
       ≡ mul (I H) (red_by_Stein_v2 (I (O (O H))) (I H));    // cross check: 1·9 = 3·3

// ============================================================
// Sub-add identity (Coq's Pos.sub_add): when q < p, q + (p - q) = p.
// We prove the form needed for the (I a, I b) case of ggcd:
//   compare a b = Lt → add (I a) (O (sub b a)) = I b.

// Successor of pred_double (Zgcd-local copy of Pos.succ_pos_pred_double).
opaque symbol succ_pred_double_local x : π (succ (pred_double x) = O x) ≔
begin
  induction
  // x = I y
  { assume y IH; reflexivity }
  // x = O y
  { assume y IH; simplify; rewrite IH; reflexivity }
  // x = H
  { reflexivity }
end;

// sub of a positive by H: succ (sub p H) = p when p ≠ H.
// Encoded without a hypothesis by case analysis on p's constructor:
// for I _ and O _ it holds, for H both sides degenerate (and is unused).
opaque symbol succ_sub_H_I x : π (succ (sub (I x) H) = I x) ≔
begin
  assume x; reflexivity
end;

opaque symbol succ_sub_H_O x : π (succ (sub (O x) H) = O x) ≔
begin
  assume x; simplify; refine succ_pred_double_local x
end;

// ============================================================
// Mask discriminators and Prop-level case eliminator.
// `mask_inv m P Q` is `P` if m is IsNul, `Q r` if m is IsPos r, and `⊤` for
// IsNeg. This lets us state the sub_mask invariants without `⇒` inside the
// proposition, so the proof can proceed by direct rewriting once we case
// on m via ind_Mask.

symbol mask_inv : Mask → Prop → (ℙ → Prop) → Prop;
rule mask_inv IsNul $P _ ↪ $P
with mask_inv (IsPos $r) _ $Q ↪ $Q $r
with mask_inv IsNeg _ _ ↪ ⊤;

// ============================================================
// Combined sub_mask / sub_mask_carry invariants.
//   - if sub_mask p q reduces to IsNul, then p = q;
//   - if sub_mask p q reduces to IsPos r, then p = add q r;
//   - if sub_mask_carry p q reduces to IsNul, then p = succ q;
//   - if sub_mask_carry p q reduces to IsPos r, then p = succ (add q r).
// IsNeg cases hold trivially (⊤).
opaque symbol sub_mask_invariants p q : π (
  mask_inv (sub_mask p q) (p = q) (λ r, p = add q r) ∧
  mask_inv (sub_mask_carry p q) (p = succ q) (λ r, p = succ (add q r))
) ≔
begin
  induction
  // p = I a
  { assume a IH;
    induction
    // q = I b
    { assume b IHb;
      apply ∧ᵢ
      { refine ind_Mask
          (λ m, mask_inv m (a = b) (λ r, a = add b r) ⇒
                mask_inv (double_mask m) (I a = I b) (λ r, I a = add (I b) r))
          _ _ _ (sub_mask a b) (∧ₑ₁ (IH b))
        { assume h; apply feq I; refine h }
        { assume x h; apply feq I; refine h }
        { assume hxx; refine ⊤ᵢ } }
      { refine ind_Mask
          (λ m, mask_inv m (a = succ b) (λ r, a = succ (add b r)) ⇒
                mask_inv (suc_double_mask m) (I a = succ (I b)) (λ r, I a = succ (add (I b) r)))
          _ _ _ (sub_mask_carry a b) (∧ₑ₂ (IH b))
        { assume h; simplify; apply feq I; refine h }
        { assume x h; simplify; apply feq I; rewrite h; rewrite succ_add; reflexivity }
        { assume hxx; refine ⊤ᵢ } } }
    // q = O b
    { assume b IHb;
      apply ∧ᵢ
      { refine ind_Mask
          (λ m, mask_inv m (a = b) (λ r, a = add b r) ⇒
                mask_inv (suc_double_mask m) (I a = O b) (λ r, I a = add (O b) r))
          _ _ _ (sub_mask a b) (∧ₑ₁ (IH b))
        { assume h; simplify; apply feq I; refine h }
        { assume x h; simplify; apply feq I; refine h }
        { assume hxx; refine ⊤ᵢ } }
      { refine ind_Mask
          (λ m, mask_inv m (a = b) (λ r, a = add b r) ⇒
                mask_inv (double_mask m) (I a = succ (O b)) (λ r, I a = succ (add (O b) r)))
          _ _ _ (sub_mask a b) (∧ₑ₁ (IH b))
        { assume h; simplify; apply feq I; refine h }
        { assume x h; simplify; apply feq I; refine h }
        { assume hxx; refine ⊤ᵢ } } }
    // q = H
    { apply ∧ᵢ
      { simplify; reflexivity }
      // sub_mask_carry (I a) H = IsPos (pred_double a). Goal: I a = succ (succ (pred_double a)).
      { simplify;
        refine ind_ℙ (λ x, I x = succ (succ (pred_double x))) _ _ _ a
        // a = I y
        { assume y IHy; reflexivity }
        // a = O y
        { assume y IHy; simplify; rewrite succ_pred_double_local; reflexivity }
        // a = H
        { reflexivity } } } }
  // p = O a
  { assume a IH;
    induction
    // q = I b
    { assume b IHb;
      apply ∧ᵢ
      { refine ind_Mask
          (λ m, mask_inv m (a = succ b) (λ r, a = succ (add b r)) ⇒
                mask_inv (suc_double_mask m) (O a = I b) (λ r, O a = add (I b) r))
          _ _ _ (sub_mask_carry a b) (∧ₑ₂ (IH b))
        { assume h; simplify; apply feq O; refine h }
        { assume x h; simplify; apply feq O; rewrite h; rewrite succ_add; reflexivity }
        { assume hxx; refine ⊤ᵢ } }
      { refine ind_Mask
          (λ m, mask_inv m (a = succ b) (λ r, a = succ (add b r)) ⇒
                mask_inv (double_mask m) (O a = succ (I b)) (λ r, O a = succ (add (I b) r)))
          _ _ _ (sub_mask_carry a b) (∧ₑ₂ (IH b))
        { assume h; simplify; apply feq O; refine h }
        { assume x h; simplify; apply feq O; refine h }
        { assume hxx; refine ⊤ᵢ } } }
    // q = O b
    { assume b IHb;
      apply ∧ᵢ
      { refine ind_Mask
          (λ m, mask_inv m (a = b) (λ r, a = add b r) ⇒
                mask_inv (double_mask m) (O a = O b) (λ r, O a = add (O b) r))
          _ _ _ (sub_mask a b) (∧ₑ₁ (IH b))
        { assume h; apply feq O; refine h }
        { assume x h; simplify; apply feq O; refine h }
        { assume hxx; refine ⊤ᵢ } }
      { refine ind_Mask
          (λ m, mask_inv m (a = succ b) (λ r, a = succ (add b r)) ⇒
                mask_inv (suc_double_mask m) (O a = succ (O b)) (λ r, O a = succ (add (O b) r)))
          _ _ _ (sub_mask_carry a b) (∧ₑ₂ (IH b))
        { assume h; simplify; apply feq O; refine h }
        { assume x h; simplify; apply feq O; rewrite h; rewrite succ_add; reflexivity }
        { assume hxx; refine ⊤ᵢ } } }
    // q = H
    { apply ∧ᵢ
      { simplify; rewrite succ_pred_double_local; reflexivity }
      // sub_mask_carry (O a) H = double_pred_mask a — case on a
      { refine ind_ℙ
          (λ x, mask_inv (double_pred_mask x) (O x = succ H) (λ r, O x = succ (add H r)))
          _ _ _ a
        // a = I y
        { assume y IHy; simplify; reflexivity }
        // a = O y
        { assume y IHy; simplify; rewrite succ_pred_double_local; reflexivity }
        // a = H
        { simplify; reflexivity } } } }
  // p = H
  { induction
    // q = I b
    { assume b IHb; apply ∧ᵢ { simplify; refine ⊤ᵢ } { simplify; refine ⊤ᵢ } }
    // q = O b
    { assume b IHb; apply ∧ᵢ { simplify; refine ⊤ᵢ } { simplify; refine ⊤ᵢ } }
    // q = H
    { apply ∧ᵢ { simplify; reflexivity } { simplify; refine ⊤ᵢ } } }
end;

// ============================================================
// Compare-related helpers needed to derive sub_add_lt from sub_mask_invariants.

// compare_acc x c x reduces to c (any positive compared with itself yields the
// accumulator). Proof by induction on x.
opaque symbol compare_acc_refl x : Π c, π (compare_acc x c x = c) ≔
begin
  induction
  { assume x h c; simplify; refine h c }
  { assume x h c; simplify; refine h c }
  { assume c; reflexivity }
end;

// Corollary: compare x x = Eq.
opaque symbol compare_refl x : π (compare x x = Eq) ≔
begin
  assume x; refine compare_acc_refl x Eq
end;

// Discriminator for Mask: true on IsNeg, false otherwise.
// ind_eq lifts (istrue ∘ isIsNeg) from RHS to LHS: ⊤ᵢ at IsNeg yields ⊥ at IsNul/IsPos.
symbol isIsNeg : Mask → 𝔹;
rule isIsNeg IsNul ↪ false
with isIsNeg (IsPos _) ↪ false
with isIsNeg IsNeg ↪ true;

opaque symbol IsNul≠IsNeg : π (IsNul ≠ IsNeg) ≔
begin
  assume h; refine ind_eq h (λ m, istrue (isIsNeg m)) ⊤ᵢ
end;

opaque symbol IsPos≠IsNeg x : π (IsPos x ≠ IsNeg) ≔
begin
  assume x h; refine ind_eq h (λ m, istrue (isIsNeg m)) ⊤ᵢ
end;

// double_mask / suc_double_mask preserve "IsNeg-ness". I.e., the only way
// for the wrapper to be IsNeg is for the input to already be IsNeg.

opaque symbol double_mask_IsNeg_inv m : π (double_mask m = IsNeg ⇒ m = IsNeg) ≔
begin
  refine ind_Mask (λ m, double_mask m = IsNeg ⇒ m = IsNeg) _ _ _
  { assume h; apply ⊥ₑ; refine IsNul≠IsNeg h }     // double_mask IsNul = IsNul ≠ IsNeg
  { assume x h; apply ⊥ₑ; refine IsPos≠IsNeg (O x) h }
  { assume hxxx; reflexivity }
end;

opaque symbol suc_double_mask_IsNeg_inv m : π (suc_double_mask m = IsNeg ⇒ m = IsNeg) ≔
begin
  refine ind_Mask (λ m, suc_double_mask m = IsNeg ⇒ m = IsNeg) _ _ _
  { assume h; apply ⊥ₑ; refine IsPos≠IsNeg H h }    // suc_double_mask IsNul = IsPos H
  { assume x h; apply ⊥ₑ; refine IsPos≠IsNeg (I x) h }
  { assume hxxx; reflexivity }
end;

// double_pred_mask a is never IsNeg (rules out the (O a, H) carry case).
opaque symbol double_pred_mask_not_IsNeg a : π (double_pred_mask a ≠ IsNeg) ≔
begin
  refine ind_ℙ (λ a, double_pred_mask a ≠ IsNeg) _ _ _
  { assume y IHy h; refine IsPos≠IsNeg (O (O y)) h }
  { assume y IHy h; refine IsPos≠IsNeg (O (pred_double y)) h }
  { assume h; refine IsNul≠IsNeg h }
end;

// Mutually-recursive correspondence between sub_mask/sub_mask_carry and
// compare. The IsNeg cases of the sub-masks correspond to the strict (Lt)
// and the non-strict (Lt ∨ Eq) sides of compare, respectively.
opaque symbol sub_mask_neg_compare p q : π (
  (sub_mask p q = IsNeg ⇒ compare p q = Lt) ∧
  (sub_mask_carry p q = IsNeg ⇒ compare p q = Lt ∨ compare p q = Eq)
) ≔
begin
  induction
  // p = I a
  { assume a IH;
    induction
    // q = I b
    { assume b IHb;
      apply ∧ᵢ
      { assume hsub;
        // double_mask (sub_mask a b) = IsNeg → sub_mask a b = IsNeg
        have ha : π (sub_mask a b = IsNeg)
          { refine double_mask_IsNeg_inv (sub_mask a b) hsub };
        // compare (I a) (I b) reduces to compare a b
        simplify; refine (∧ₑ₁ (IH b)) ha }
      { assume hsub;
        have ha : π (sub_mask_carry a b = IsNeg)
          { refine suc_double_mask_IsNeg_inv (sub_mask_carry a b) hsub };
        simplify; refine (∧ₑ₂ (IH b)) ha } }
    // q = O b
    { assume b IHb;
      apply ∧ᵢ
      { assume hsub;
        have ha : π (sub_mask a b = IsNeg)
          { refine suc_double_mask_IsNeg_inv (sub_mask a b) hsub };
        // compare (I a) (O b) = compare_acc a Gt b = case_Comp (compare a b) Gt Lt Gt
        have hab : π (compare a b = Lt) { refine (∧ₑ₁ (IH b)) ha };
        simplify; rewrite compare_Gt; rewrite hab; reflexivity }
      { assume hsub;
        have ha : π (sub_mask a b = IsNeg)
          { refine double_mask_IsNeg_inv (sub_mask a b) hsub };
        have hab : π (compare a b = Lt) { refine (∧ₑ₁ (IH b)) ha };
        apply ∨ᵢ₁; simplify; rewrite compare_Gt; rewrite hab; reflexivity } }
    // q = H
    { apply ∧ᵢ
      { assume hsub; apply ⊥ₑ; refine IsPos≠IsNeg (O a) hsub }
      { assume hsub; apply ⊥ₑ; refine IsPos≠IsNeg (pred_double a) hsub } } }
  // p = O a
  { assume a IH;
    induction
    // q = I b
    { assume b IHb;
      apply ∧ᵢ
      { assume hsub;
        have ha : π (sub_mask_carry a b = IsNeg)
          { refine suc_double_mask_IsNeg_inv (sub_mask_carry a b) hsub };
        // From IH carry: compare a b = Lt ∨ Eq.
        // compare (O a) (I b) = compare_acc a Lt b = case_Comp (compare a b) Lt Lt Gt = Lt in both cases.
        simplify; rewrite compare_Lt;
        refine ∨ₑ ((∧ₑ₂ (IH b)) ha) _ _
          { assume h; rewrite h; reflexivity }
          { assume h; rewrite h; reflexivity } }
      { assume hsub;
        have ha : π (sub_mask_carry a b = IsNeg)
          { refine double_mask_IsNeg_inv (sub_mask_carry a b) hsub };
        apply ∨ᵢ₁; simplify; rewrite compare_Lt;
        refine ∨ₑ ((∧ₑ₂ (IH b)) ha) _ _
          { assume h; rewrite h; reflexivity }
          { assume h; rewrite h; reflexivity } } }
    // q = O b
    { assume b IHb;
      apply ∧ᵢ
      { assume hsub;
        have ha : π (sub_mask a b = IsNeg)
          { refine double_mask_IsNeg_inv (sub_mask a b) hsub };
        simplify; refine (∧ₑ₁ (IH b)) ha }
      { assume hsub;
        have ha : π (sub_mask_carry a b = IsNeg)
          { refine suc_double_mask_IsNeg_inv (sub_mask_carry a b) hsub };
        simplify; refine (∧ₑ₂ (IH b)) ha } }
    // q = H
    { apply ∧ᵢ
      { assume hsub; apply ⊥ₑ; refine IsPos≠IsNeg (pred_double a) hsub }
      { assume hsub; apply ⊥ₑ; refine double_pred_mask_not_IsNeg a hsub } } }
  // p = H
  { induction
    // q = I b
    { assume b IHb;
      apply ∧ᵢ
      { assume hxxx; reflexivity }
      { assume hh; apply ∨ᵢ₁; reflexivity } }
    // q = O b
    { assume b IHb;
      apply ∧ᵢ
      { assume hxxx; reflexivity }
      { assume hh; apply ∨ᵢ₁; reflexivity } }
    // q = H
    { apply ∧ᵢ
      { assume hsub; apply ⊥ₑ; refine IsNul≠IsNeg hsub }
      { assume hh; apply ∨ᵢ₂; reflexivity } } }
end;

// ============================================================
// sub_add_lt and sub_add_gt: the form of the sub-add identity directly
// consumed by ggcd_step_II_correct.
//
// sub_add_lt: when a < b, (I a) + 2·(b - a) = I b.
// Equivalently: I (add a (sub b a)) = I b, i.e., add a (sub b a) = b.
//
// Proof: case on sub_mask b a via ind_Mask, using
//   1. sub_mask_invariants: if sub_mask b a = IsPos r, then b = add a r;
//   2. sub_mask_invariants + compare_refl: rules out sub_mask b a = IsNul
//      (would force b = a, contradicting compare a b = Lt);
//   3. sub_mask_neg_compare: rules out sub_mask b a = IsNeg
//      (would give compare b a = Lt, contradicting compare a b = Lt via opp).

opaque symbol sub_add_lt :
  Π a b, π (compare a b = Lt) → π (add (I a) (O (sub b a)) = I b) ≔
begin
  assume a b hlt;
  refine ind_Mask
    (λ m, sub_mask b a = m ⇒ add (I a) (O (sub' m)) = I b)
    _ _ _ (sub_mask b a) (eq_refl _)
  // m = IsNul: sub_mask b a = IsNul → b = a → compare a a = Eq, contradicts hlt
  { assume heq;
    apply ⊥ₑ;
    // Pull `b = a` out of mask_inv at IsNul by substituting heq into the invariant.
    have hba : π (b = a)
      { refine ind_eq (eq_sym heq)
          (λ m, mask_inv m (b = a) (λ r, b = add a r))
          (∧ₑ₁ (sub_mask_invariants b a)) };
    have hcab : π (compare a b = Eq)
      { rewrite hba; refine compare_refl a };
    refine Lt≠Eq (ind_eq (eq_sym hlt) (λ x, x = Eq) hcab) }
  // m = IsPos r: sub_mask b a = IsPos r → b = add a r → add (I a) (O r) = I (add a r) = I b
  { assume r heq;
    simplify;
    have hba : π (b = add a r)
      { refine ind_eq (eq_sym heq)
          (λ m, mask_inv m (b = a) (λ r0, b = add a r0))
          (∧ₑ₁ (sub_mask_invariants b a)) };
    rewrite left hba; reflexivity }
  // m = IsNeg: sub_mask b a = IsNeg → compare b a = Lt → compare a b = Gt, contradicts hlt
  { assume heq;
    apply ⊥ₑ;
    have hba : π (compare b a = Lt) { refine (∧ₑ₁ (sub_mask_neg_compare b a)) heq };
    // compare a b = opp (compare b a) = opp Lt = Gt
    have habGt : π (compare a b = Gt)
      { rewrite compare_com; rewrite hba; reflexivity };
    refine Gt≠Lt (eq_sym (ind_eq (eq_sym hlt) (λ x, x = Gt) habGt)) }
end;

// sub_add_gt: symmetric, derived from sub_add_lt by swapping a and b.
//   compare a b = Gt ⇔ compare b a = Lt (by compare_com),
// so sub_add_gt a b h = sub_add_lt b a (derived hypothesis).
opaque symbol sub_add_gt :
  Π a b, π (compare a b = Gt) → π (add (I b) (O (sub a b)) = I a) ≔
begin
  assume a b hgt;
  // compare b a = opp (compare a b) = opp Gt = Lt
  have hba : π (compare b a = Lt)
    { rewrite compare_com; rewrite hgt; reflexivity };
  refine sub_add_lt b a hba
end;

// ============================================================
// Correctness of ggcd_fuel: for any n, x, y, letting (g, aa, bb) =
// ggcd_fuel n x y, we have x = g·aa and y = g·bb. Stated as a joint
// conjunction so the induction can use both parts of the IH at once.

// Helper used in the (I a, I b) branch: case-analyzes on a Comp result.
// For Eq: the body returns (I a, H, H) immediately; compare_decides
// gives a = b, so I a = I b and both sides reduce to I a.
// For Lt/Gt: the body recurses through ggcd_fuel; needs sub-add identity.
// Parameterized on IHk (the fuel-k correctness) to avoid a forward
// reference to ggcd_fuel_correct; the caller (ggcd_fuel_correct) supplies
// its inductive hypothesis here.
opaque symbol ggcd_step_II_correct : Π k,
  (Π x y, π ((x = mul ((ggcd_fuel k x y)₁) (((ggcd_fuel k x y)₂)₁)) ∧
             (y = mul ((ggcd_fuel k x y)₁) (((ggcd_fuel k x y)₂)₂)))) →
  Π a b,
  π ((I a = mul ((ggcd_step_II k a b (compare a b))₁)
                (((ggcd_step_II k a b (compare a b))₂)₁)) ∧
     (I b = mul ((ggcd_step_II k a b (compare a b))₁)
                (((ggcd_step_II k a b (compare a b))₂)₂))) ≔
begin
  assume k IHk a b;
  refine ind_Comp
    (λ c, (compare a b = c) ⇒
          (I a = mul ((ggcd_step_II k a b c)₁)
                     (((ggcd_step_II k a b c)₂)₁)) ∧
          (I b = mul ((ggcd_step_II k a b c)₁)
                     (((ggcd_step_II k a b c)₂)₂)))
    _ _ _
    (compare a b) _
  // P Eq
  { assume heq;
    have aeqb : π (a = b) { refine compare_decides a b heq };
    apply ∧ᵢ
    { reflexivity }
    { rewrite left aeqb; reflexivity } }
  // P Lt
  { assume hlt;
    simplify;
    apply ∧ᵢ
    { refine ∧ₑ₂ (IHk (sub' (sub_mask b a)) (I a)) }
    { rewrite mul_distr_l;
      rewrite mul_O_right;
      rewrite left (∧ₑ₂ (IHk (sub' (sub_mask b a)) (I a)));
      rewrite left (∧ₑ₁ (IHk (sub' (sub_mask b a)) (I a)));
      symmetry; refine sub_add_lt a b hlt } }
  // P Gt
  { assume hgt;
    simplify;
    apply ∧ᵢ
    { rewrite mul_distr_l;
      rewrite mul_O_right;
      rewrite left (∧ₑ₂ (IHk (sub' (sub_mask a b)) (I b)));
      rewrite left (∧ₑ₁ (IHk (sub' (sub_mask a b)) (I b)));
      symmetry; refine sub_add_gt a b hgt }
    { refine ∧ₑ₂ (IHk (sub' (sub_mask a b)) (I b)) } }
  // compare a b = compare a b
  { reflexivity }
end;

opaque symbol ggcd_fuel_correct : Π n x y,
  π ((x = mul ((ggcd_fuel n x y)₁) (((ggcd_fuel n x y)₂)₁)) ∧
     (y = mul ((ggcd_fuel n x y)₁) (((ggcd_fuel n x y)₂)₂))) ≔
begin
  induction
  // n = 0: ggcd_fuel 0 x y → (H, x, y). g = H, aa = x, bb = y.
  // mul H x = x, mul H y = y, so both equalities are reflexive.
  { assume x y; apply ∧ᵢ { reflexivity } { reflexivity } }
  // n = succ k
  { assume k IHk;
    induction
    // x = I a
    { assume a IH_xa;
      induction
      // y = I b — dispatches to ggcd_step_II; use ggcd_step_II_correct
      { assume b IH_yb; refine ggcd_step_II_correct k IHk a b }
      // y = O b — recurse to ggcd_fuel k (I a) b
      { assume b IH_yb; simplify; apply ∧ᵢ
        { refine ∧ₑ₁ (IHk (I a) b) }
        { rewrite mul_O_right; refine feq O _; refine ∧ₑ₂ (IHk (I a) b) } }
      // y = H — base case via rule 3
      { apply ∧ᵢ { reflexivity } { reflexivity } } }
    // x = O a
    { assume a IH_xa;
      induction
      // y = I b — recurse to ggcd_fuel k a (I b)
      { assume b IH_yb; simplify; apply ∧ᵢ
        { rewrite mul_O_right; refine feq O _; refine ∧ₑ₁ (IHk a (I b)) }
        { refine ∧ₑ₂ (IHk a (I b)) } }
      // y = O b — recurse to ggcd_fuel k a b
      { assume b IH_yb; simplify; apply ∧ᵢ
        { refine feq O _; refine ∧ₑ₁ (IHk a b) }
        { refine feq O _; refine ∧ₑ₂ (IHk a b) } }
      // y = H — base case via rule 3
      { apply ∧ᵢ { reflexivity } { reflexivity } } }
    // x = H — base case via rule 2
    { assume y; apply ∧ᵢ { reflexivity } { reflexivity } } }
end;
// ============================================================
// Symmetry of ggcd_fuel: swapping the two arguments yields the same gcd
// (first projection) and swaps the (second, third) projections.
//
// Used (with ggcd_fuel_correct) to derive the cross identity for
// red_by_Stein_v2: aa(x,y) · y = x · aa(y,x), via the chain
//   aa·y = aa·(g·bb) = (g·aa)·bb = x·bb = x·aa(y,x).
//
// The (I a, I b) case dispatches to ggcd_step_II_sym; the other cases
// recurse via the inductive hypothesis IHk.

opaque symbol ggcd_step_II_sym : Π k a b, π (
  (((ggcd_step_II k a b (compare a b))₁) = ((ggcd_step_II k b a (compare b a))₁)) ∧
  ((((ggcd_step_II k a b (compare a b))₂)₁) = (((ggcd_step_II k b a (compare b a))₂)₂))
) ≔
begin
  assume k a b;
  // Express compare b a in terms of compare a b so a single ind_Comp covers both.
  have hcom : π (compare b a = opp (compare a b)) { refine compare_com a b };
  rewrite hcom;
  refine ind_Comp
    (λ c, (compare a b = c) ⇒
      ( (((ggcd_step_II k a b c)₁) = ((ggcd_step_II k b a (opp c))₁)) ∧
        ((((ggcd_step_II k a b c)₂)₁) = (((ggcd_step_II k b a (opp c))₂)₂)) ))
    _ _ _
    (compare a b) (eq_refl _)
  // c = Eq: compare_decides gives a = b, so I a = I b
  { assume heq;
    have hab : π (a = b) { refine compare_decides a b heq };
    apply ∧ᵢ
    { simplify; apply feq I; refine hab }
    { simplify; reflexivity } }
  // c = Lt: opp Lt = Gt. Both step_IIs share r ≔ ggcd_fuel k (sub b a) (I a).
  { assume hlt;
    apply ∧ᵢ { simplify; reflexivity } { simplify; reflexivity } }
  // c = Gt: opp Gt = Lt. Both step_IIs share r ≔ ggcd_fuel k (sub a b) (I b).
  { assume hgt;
    apply ∧ᵢ { simplify; reflexivity } { simplify; reflexivity } }
end;

opaque symbol ggcd_fuel_sym : Π n x y, π (
  (((ggcd_fuel n x y)₁) = ((ggcd_fuel n y x)₁)) ∧
  ((((ggcd_fuel n x y)₂)₁) = (((ggcd_fuel n y x)₂)₂))
) ≔
begin
  induction
  // n = 0: ggcd_fuel 0 x y = (H, x, y); ggcd_fuel 0 y x = (H, y, x).
  { assume x y; apply ∧ᵢ { reflexivity } { reflexivity } }
  // n = k+1
  { assume k IHk;
    induction
    // x = I a
    { assume a IH_xa;
      induction
      // y = I b — both compute via ggcd_step_II; use ggcd_step_II_sym.
      { assume b IH_yb; refine ggcd_step_II_sym k a b }
      // y = O b
      { assume b IH_yb;
        apply ∧ᵢ
        { refine (∧ₑ₁ (IHk (I a) b)) }
        { refine (∧ₑ₂ (IHk (I a) b)) } }
      // y = H
      { apply ∧ᵢ { reflexivity } { reflexivity } } }
    // x = O a
    { assume a IH_xa;
      induction
      // y = I b
      { assume b IH_yb;
        apply ∧ᵢ
        { refine (∧ₑ₁ (IHk a (I b))) }
        { apply feq O; refine (∧ₑ₂ (IHk a (I b))) } }
      // y = O b
      { assume b IH_yb;
        apply ∧ᵢ
        { apply feq O; refine (∧ₑ₁ (IHk a b)) }
        { refine (∧ₑ₂ (IHk a b)) } }
      // y = H
      { apply ∧ᵢ { reflexivity } { reflexivity } } }
    // x = H
    { induction
      { assume b IH_yb; apply ∧ᵢ { reflexivity } { reflexivity } }
      { assume b IH_yb; apply ∧ᵢ { reflexivity } { reflexivity } }
      { apply ∧ᵢ { reflexivity } { reflexivity } } } }
end;

// ============================================================
// Cross identity for red_by_Stein_v2: the form consumed by Z_red_Stein_correct.
//
// Mathematically: red_by_Stein_v2 x y = x / gcd(x,y), so
//   (x/gcd) · y = x · (y/gcd) — both equal x·y/gcd.
//
// Proof outline (letting n = Stdlib.Nat.+ (size_nat x) (size_nat y), aa = (ggcd_fuel n x y)₂.₁,
// bb = (ggcd_fuel n x y)₂.₂, g = (ggcd_fuel n x y)₁):
//   1. Align fuels via addnC: ggcd_safe y x uses Stdlib.Nat.+ (size_nat y) (size_nat x) = n.
//   2. Apply ggcd_fuel_sym to rewrite (ggcd_fuel n y x)₂.₁ as bb.
//   3. Goal: mul aa y = mul x bb.
//   4. From ggcd_fuel_correct: x = mul g aa and y = mul g bb.
//   5. Both sides reduce to mul g (mul aa bb) by assoc + com.

opaque symbol red_by_Stein_v2_cross x y :
  π (mul (red_by_Stein_v2 x y) y = mul x (red_by_Stein_v2 y x)) ≔
begin
  assume x y;
  // Step 1: align fuels. ggcd_safe y x uses Stdlib.Nat.+ (size_nat y) (size_nat x).
  // Rewrite to Stdlib.Nat.+ (size_nat x) (size_nat y) via addnC.
  have hfuel : π (Stdlib.Nat.+ (size_nat y) (size_nat x) = Stdlib.Nat.+ (size_nat x) (size_nat y))
    { refine addnC (size_nat y) (size_nat x) };
  simplify;
  rewrite hfuel;
  // Step 2: use ggcd_fuel_sym applied at (y, x) to substitute
  //   ((ggcd_fuel n y x)₂)₁ = ((ggcd_fuel n x y)₂)₂.
  rewrite (∧ₑ₂ (ggcd_fuel_sym (Stdlib.Nat.+ (size_nat x) (size_nat y)) y x));
  // Goal: mul ((ggcd_fuel n x y)₂)₁ y = mul x ((ggcd_fuel n x y)₂)₂.
  //
  // Let aa = ((ggcd_fuel n x y)₂)₁, bb = ((ggcd_fuel n x y)₂)₂, g = (ggcd_fuel n x y)₁.
  // From ggcd_fuel_correct: x = mul g aa, y = mul g bb.
  // Chain: mul aa y = mul aa (mul g bb)       [hy]
  //                 = mul (mul aa g) bb       [mul_assoc]
  //                 = mul (mul g aa) bb       [mul_com]
  //                 = mul x bb                [hx, reversed]
  have hx : π (x = mul ((ggcd_fuel (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y)₁)
                       (((ggcd_fuel (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y)₂)₁))
    { refine ∧ₑ₁ (ggcd_fuel_correct (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y) };
  have hy : π (y = mul ((ggcd_fuel (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y)₁)
                       (((ggcd_fuel (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y)₂)₂))
    { refine ∧ₑ₂ (ggcd_fuel_correct (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y) };
  // Substitute y → mul g bb only in the LHS's outer position (`mul _ y = _`),
  // avoiding the y inside ggcd_fuel's arguments.
  rewrite .[in v in mul _ v = _] hy;
  // Goal: mul aa (mul g bb) = mul x bb
  rewrite left mul_assoc;
  // Goal: mul (mul aa g) bb = mul x bb
  // Substitute x → mul g aa on RHS at the outer position.
  rewrite .[in v in _ = mul v _] hx;
  // Goal: mul (mul aa g) bb = mul (mul g aa) bb
  // Commute mul aa g → mul g aa.
  rewrite (mul_com (((ggcd_fuel (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y)₂)₁)
                   ((ggcd_fuel (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y)₁));
  reflexivity
end;

// ============================================================
// Z_red_Stein: reduce ℤ by gcd, keeping the sign of the first argument.
//
// Semantically Z_red_Stein a b = a / gcd(|a|, |b|) (with sign carried from a).
// Implemented on ℙ payloads via red_by_Stein_v2 (the ggcd_safe-based, total,
// terminating version). Z0 reduces to Z0; reduction by Z0 returns the sign
// of the first argument (a/|a|).
symbol Z_red_Stein : ℤ → ℤ → ℤ;
rule Z_red_Stein Z0 _ ↪ Z0
with Z_red_Stein $a Z0 ↪ sign $a
with Z_red_Stein (Zpos $a) (Zpos $b) ↪ Zpos (red_by_Stein_v2 $a $b)
with Z_red_Stein (Zpos $a) (Zneg $b) ↪ Zpos (red_by_Stein_v2 $a $b)
with Z_red_Stein (Zneg $a) (Zpos $b) ↪ Zneg (red_by_Stein_v2 $a $b)
with Z_red_Stein (Zneg $a) (Zneg $b) ↪ Zneg (red_by_Stein_v2 $a $b);

// Cross-product correctness: (a/gcd)·b = a·(b/gcd). Since the gcd is symmetric,
// this form avoids naming the gcd explicitly. Consumed by Q.lp normalization.
//
// Reduces to red_by_Stein_v2_cross on the ℙ payload in each sign combination;
// the Z0 cases close by reflexivity.
opaque symbol Z_red_Stein_correct a b :
  π (Z_red_Stein a b * b = a * Z_red_Stein b a) ≔
begin
  induction
  // a = Z0
  { induction
    { reflexivity }
    { assume y; reflexivity }
    { assume y; reflexivity } }
  // a = Zpos x
  { assume x;
    induction
    { reflexivity }
    { assume y; simplify; apply feq (Zpos); refine red_by_Stein_v2_cross x y }
    { assume y; simplify; apply feq (Zneg); refine red_by_Stein_v2_cross x y } }
  // a = Zneg x
  { assume x;
    induction
    { reflexivity }
    { assume y; simplify; apply feq (Zneg); refine red_by_Stein_v2_cross x y }
    { assume y; simplify; apply feq (Zpos); refine red_by_Stein_v2_cross x y } }
end;

// ============================================================
// PHASE 1 — Divisibility on ℤ:  d ∣ n  ≔  ∃ k, n = d * k.
// Foundation for the gcd "greatest divisor" / coprimality development.

symbol ∣ : ℤ → ℤ → Prop; notation ∣ infix 10;
rule $d ∣ $n ↪ `∃ k, $n = $d * k;

opaque symbol div_refl a : π (a ∣ a) ≔
begin
  assume a; refine ∃ᵢ 1 _; symmetry; refine *_neutral a
end;

opaque symbol div_trans a b c : π (a ∣ b) → π (b ∣ c) → π (a ∣ c) ≔
begin
  assume a b c hab hbc;
  refine ∃ₑ hab _; assume i hi;
  refine ∃ₑ hbc _; assume j hj;
  refine ∃ᵢ (i * j) _; simplify;
  rewrite hj; rewrite hi; rewrite *_assoc; reflexivity
end;

// z divides a unit ⟹ z divides anything.
opaque symbol div_of_unit z a : π (z ∣ 1) → π (z ∣ a) ≔
begin
  assume z a hz;
  refine ∃ₑ hz _; assume k hk;
  refine ∃ᵢ (a * k) _; simplify;
  rewrite *_com z (a * k);
  rewrite *_assoc a k z;
  rewrite *_com k z;
  rewrite left hk;
  symmetry; refine *_neutral a
end;

opaque symbol div_add z a b : π (z ∣ a) → π (z ∣ b) → π (z ∣ (a + b)) ≔
begin
  assume z a b ha hb;
  refine ∃ₑ ha _; assume i hi;
  refine ∃ₑ hb _; assume j hj;
  refine ∃ᵢ (i + j) _; simplify;
  rewrite *_distr_l; rewrite left hi; rewrite left hj; reflexivity
end;

// z ∣ a and z ∣ (a+b)  ⟹  z ∣ b.
opaque symbol div_add_cancel z a b : π (z ∣ a) → π (z ∣ (a + b)) → π (z ∣ b) ≔
begin
  assume z a b ha hab;
  refine ∃ₑ ha _; assume i hi;
  refine ∃ₑ hab _; assume j hj;
  refine ∃ᵢ (j + — i) _; simplify;
  rewrite *_distr_l;
  rewrite left neg_mul_r;
  rewrite left hi;
  rewrite left hj;
  rewrite +_com a b;
  rewrite +_assoc;
  rewrite -_same;
  reflexivity
end;

opaque symbol div_mul_r z a c : π (z ∣ a) → π (z ∣ (a * c)) ≔
begin
  assume z a c ha;
  refine ∃ₑ ha _; assume i hi;
  refine ∃ᵢ (i * c) _; simplify;
  rewrite hi; rewrite *_assoc; reflexivity
end;

opaque symbol div_mul_l z a c : π (z ∣ a) → π (z ∣ (c * a)) ≔
begin
  assume z a c ha;
  refine ∃ₑ ha _; assume i hi;
  refine ∃ᵢ (c * i) _; simplify;
  rewrite hi;
  rewrite left *_assoc;
  rewrite (*_com c z);
  rewrite *_assoc;
  reflexivity
end;

// Cancel a common factor of 2:  (2·u) ∣ (2·v)  ⟹  u ∣ v.
opaque symbol cancel2 u v : π ((2 * u) ∣ (2 * v)) → π (u ∣ v) ≔
begin
  assume u v h;
  refine ∃ₑ h _; assume k hk;
  refine ∃ᵢ k _; simplify;
  refine *_reg_r v (u * k) 2 _ _
  { refine Zpos≠Z0 (O H) }
  { rewrite *_com v 2;
    rewrite hk;
    rewrite *_com (u * k) 2;
    rewrite *_assoc;
    reflexivity }
end;

// ============================================================
// PHASE 2a — ℙ↔ℤ divisibility for positives, and the factor-2 Euclid step.

symbol unZpos : ℤ → ℙ;
rule unZpos (Zpos $p) ↪ $p
with unZpos Z0 ↪ H
with unZpos (Zneg $p) ↪ $p;

opaque symbol Zpos_inj m m' : π (Zpos m = Zpos m') → π (m = m') ≔
begin
  assume m m' h; refine feq unZpos h
end;

// Divisibility of positives is the same as ℙ-level multiplicative divisibility.
opaque symbol divp_intro p m k : π (m = mul p k) → π (Zpos p ∣ Zpos m) ≔
begin
  assume p m k h; refine ∃ᵢ (Zpos k) _; rewrite h; reflexivity
end;

opaque symbol divp_elim p m : π (Zpos p ∣ Zpos m) → π (`∃ k, m = mul p k) ≔
begin
  assume p m h;
  refine ∃ₑ h _;
  induction
  // k = Z0
  { assume hk; apply ⊥ₑ; refine Zpos≠Z0 m hk }
  // k = Zpos k'
  { assume k' hk; refine ∃ᵢ k' _; refine Zpos_inj m (mul p k') hk }
  // k = Zneg k'
  { assume k' hk; apply ⊥ₑ; refine Zpos≠Zneg m (mul p k') hk }
end;

// Factor-2 Euclid: an odd divisor of an even number divides its half.
opaque symbol eucl2_I q a : π (Zpos (I q) ∣ Zpos (O a)) → π (Zpos (I q) ∣ Zpos a) ≔
begin
  assume q a h;
  have he : π (`∃ k, O a = mul (I q) k) { refine divp_elim (I q) (O a) h };
  refine ∃ₑ he _;
  induction
  // k = I k': mul (I q) (I k') is odd, contradicting O a
  { assume k' IH hk;
    apply ⊥ₑ;
    have hc : π (I (add q (mul (I q) k')) = O a)
      { symmetry; rewrite hk; rewrite mul_I_right; reflexivity };
    refine I≠O hc }
  // k = O k': O a = O (mul (I q) k') ⟹ a = mul (I q) k'
  { assume k' IH hk;
    refine divp_intro (I q) a k' _;
    refine O_inj a (mul (I q) k') _;
    rewrite hk; rewrite mul_O_right; reflexivity }
  // k = H: O a = I q, impossible
  { assume hk;
    apply ⊥ₑ;
    have hc : π (I q = O a) { symmetry; rewrite hk; reflexivity };
    refine I≠O hc }
end;

// An even number cannot divide an odd number.
opaque symbol even_div_odd_false q a : π (Zpos (O q) ∣ Zpos (I a)) → π ⊥ ≔
begin
  assume q a h;
  have he : π (`∃ k, I a = mul (O q) k) { refine divp_elim (O q) (I a) h };
  refine ∃ₑ he _;
  assume k hk;
  have hc : π (I a = O (mul q k)) { rewrite hk; reflexivity };
  refine I≠O hc
end;

// ============================================================
// PHASE 2b — fuel-bound bookkeeping (ℕ/size) then ggcd_fuel_greatest.

// m ≤ m + n  on ℕ.
opaque symbol leq_addr m n : π (istrue (Stdlib.Nat.≤ m (Stdlib.Nat.+ m n))) ≔
begin
  induction
  { assume n0; refine ⊤ᵢ }
  { assume m' IH n0; refine IH n0 }
end;

// size_nat is always ≥ 1.
opaque symbol size_pos p : π (istrue (Stdlib.Nat.≤ (_0 +1) (size_nat p))) ≔
begin
  induction
  { assume p' IH; refine ⊤ᵢ }
  { assume p' IH; refine ⊤ᵢ }
  { refine ⊤ᵢ }
end;

// size_nat x + size_nat y ≥ 1 (used to make the n=0 fuel case vacuous).
opaque symbol size_sum_pos x y :
  π (istrue (Stdlib.Nat.≤ (_0 +1) (Stdlib.Nat.+ (size_nat x) (size_nat y)))) ≔
begin
  assume x y;
  refine @leq_trans (_0 +1) (size_nat x) (Stdlib.Nat.+ (size_nat x) (size_nat y))
    (size_pos x) (leq_addr (size_nat x) (size_nat y))
end;

// size is non-decreasing under successor.
opaque symbol size_succ_ge q : π (istrue (Stdlib.Nat.≤ (size_nat q) (size_nat (succ q)))) ≔
begin
  induction
  { assume q' IH; refine IH }
  { assume q' IH; refine Stdlib.Nat.≤_refl (size_nat q' +1) }
  { refine ⊤ᵢ }
end;

// size of the right summand ≤ size of the sum.
opaque symbol size_add_ge_r p q :
  π (istrue (Stdlib.Nat.≤ (size_nat q) (size_nat (add p q)))) ≔
begin
  assume p q;
  refine ind_ℙeano (λ p0, istrue (Stdlib.Nat.≤ (size_nat q) (size_nat (add p0 q)))) _ _ p
  { refine size_succ_ge q }
  { assume p' IH; rewrite add_succ;
    refine @leq_trans (size_nat q) (size_nat (add p' q)) (size_nat (succ (add p' q)))
      IH (size_succ_ge (add p' q)) }
end;

// size of a (valid, a<b) difference does not exceed the minuend's size.
opaque symbol size_sub_le a b :
  π (compare a b = Lt) → π (istrue (Stdlib.Nat.≤ (size_nat (sub b a)) (size_nat b))) ≔
begin
  assume a b hlt;
  have key : π (istrue (Stdlib.Nat.≤ (size_nat (O (sub b a))) (size_nat (I b))))
    { rewrite left (sub_add_lt a b hlt); refine size_add_ge_r (I a) (O (sub b a)) };
  refine key
end;

// 1 divides everything.
opaque symbol div_H_all m : π (Zpos H ∣ Zpos m) ≔
begin
  assume m; refine divp_intro H m m _; reflexivity
end;

// Doubling preserves divisibility:  u ∣ v  ⟹  2·u ∣ 2·v.
opaque symbol mul2_div u v : π (u ∣ v) → π ((2 * u) ∣ (2 * v)) ≔
begin
  assume u v h;
  refine ∃ₑ h _; assume k hk;
  refine ∃ᵢ k _; simplify;
  rewrite hk; rewrite *_assoc; reflexivity
end;

// ---- per-shape fuel-bound lemmas: bound at k+1 for the node ⟹ bound at k
//      for the recursive subcall's inputs. ----

opaque symbol bnd_OO a b k :
  π (istrue (Stdlib.Nat.≤ (Stdlib.Nat.+ (size_nat (O a)) (size_nat (O b))) (k +1))) →
  π (istrue (Stdlib.Nat.≤ (Stdlib.Nat.+ (size_nat a) (size_nat b)) k)) ≔
begin
  assume a b k h;
  have h' : π (istrue (Stdlib.Nat.≤ (Stdlib.Nat.+ (size_nat a) (size_nat b +1)) k)) { refine h };
  refine @leq_trans (Stdlib.Nat.+ (size_nat a) (size_nat b))
                    (Stdlib.Nat.+ (size_nat a) (size_nat b +1)) k
                    (∧ₑ₂ (leq_add2l (size_nat a) (size_nat b) (size_nat b +1)) (leqnSn (size_nat b)))
                    h'
end;

opaque symbol bnd_IO a b k :
  π (istrue (Stdlib.Nat.≤ (Stdlib.Nat.+ (size_nat (I a)) (size_nat (O b))) (k +1))) →
  π (istrue (Stdlib.Nat.≤ (Stdlib.Nat.+ (size_nat (I a)) (size_nat b)) k)) ≔
begin
  assume a b k h;
  have h' : π (istrue (Stdlib.Nat.≤ (Stdlib.Nat.+ (size_nat a) (size_nat b +1)) k)) { refine h };
  simplify;
  rewrite left (addnS (size_nat a) (size_nat b));
  refine h'
end;

opaque symbol bnd_OI a b k :
  π (istrue (Stdlib.Nat.≤ (Stdlib.Nat.+ (size_nat (O a)) (size_nat (I b))) (k +1))) →
  π (istrue (Stdlib.Nat.≤ (Stdlib.Nat.+ (size_nat a) (size_nat (I b))) k)) ≔
begin
  assume a b k h; refine h
end;

opaque symbol bnd_IIlt a b k :
  π (compare a b = Lt) →
  π (istrue (Stdlib.Nat.≤ (Stdlib.Nat.+ (size_nat (I a)) (size_nat (I b))) (k +1))) →
  π (istrue (Stdlib.Nat.≤ (Stdlib.Nat.+ (size_nat (sub b a)) (size_nat (I a))) k)) ≔
begin
  assume a b k hlt h;
  have hk : π (istrue (Stdlib.Nat.≤ (Stdlib.Nat.+ (size_nat a) (size_nat b) +1) k))
    { rewrite left (addnS (size_nat a) (size_nat b)); refine h };
  have hs : π (istrue (Stdlib.Nat.≤ (size_nat (sub b a)) (size_nat b)))
    { refine size_sub_le a b hlt };
  have hsa : π (istrue (Stdlib.Nat.≤ (Stdlib.Nat.+ (size_nat (sub b a)) (size_nat a))
                                     (Stdlib.Nat.+ (size_nat a) (size_nat b))))
    { rewrite (addnC (size_nat a) (size_nat b));
      refine ∧ₑ₂ (leq_add2r (size_nat a) (size_nat (sub b a)) (size_nat b)) hs };
  simplify;
  refine @leq_trans (Stdlib.Nat.+ (size_nat (sub b a)) (size_nat a) +1)
                    (Stdlib.Nat.+ (size_nat a) (size_nat b) +1) k hsa hk
end;

opaque symbol bnd_IIgt a b k :
  π (compare a b = Gt) →
  π (istrue (Stdlib.Nat.≤ (Stdlib.Nat.+ (size_nat (I a)) (size_nat (I b))) (k +1))) →
  π (istrue (Stdlib.Nat.≤ (Stdlib.Nat.+ (size_nat (sub a b)) (size_nat (I b))) k)) ≔
begin
  assume a b k hgt h;
  have hlt' : π (compare b a = Lt) { rewrite compare_com; rewrite hgt; reflexivity };
  have hk : π (istrue (Stdlib.Nat.≤ (Stdlib.Nat.+ (size_nat a) (size_nat b) +1) k))
    { rewrite left (addnS (size_nat a) (size_nat b)); refine h };
  have hs : π (istrue (Stdlib.Nat.≤ (size_nat (sub a b)) (size_nat a)))
    { refine size_sub_le b a hlt' };
  have hsa : π (istrue (Stdlib.Nat.≤ (Stdlib.Nat.+ (size_nat (sub a b)) (size_nat b))
                                     (Stdlib.Nat.+ (size_nat a) (size_nat b))))
    { refine ∧ₑ₂ (leq_add2r (size_nat b) (size_nat (sub a b)) (size_nat a)) hs };
  simplify;
  refine @leq_trans (Stdlib.Nat.+ (size_nat (sub a b)) (size_nat b) +1)
                    (Stdlib.Nat.+ (size_nat a) (size_nat b) +1) k hsa hk
end;

// ============================================================
// ggcd_fuel_greatest: with enough fuel, the gcd component is divisible by
// every common (positive) divisor of the inputs.
opaque symbol ggcd_fuel_greatest : Π n x y z,
  π (istrue (Stdlib.Nat.≤ (Stdlib.Nat.+ (size_nat x) (size_nat y)) n)) →
  π (Zpos z ∣ Zpos x) → π (Zpos z ∣ Zpos y) →
  π (Zpos z ∣ Zpos ((ggcd_fuel n x y)₁)) ≔
begin
  induction
  // n = 0 : the fuel bound is impossible (size sum ≥ 1)
  { assume x y z hbound hx hy;
    apply ⊥ₑ;
    refine @leq_trans (_0 +1) (Stdlib.Nat.+ (size_nat x) (size_nat y)) _0
      (size_sum_pos x y) hbound }
  // n = k+1
  { assume k IHk;
    induction
    // x = I a
    { assume a IH_xa;
      induction
      // y = I b
      { assume b IH_yb;
        induction
        // z = I z'
        { assume z' IHz hbound hx hy;
          refine ind_Comp
            (λ c, (compare a b = c) ⇒ (Zpos (I z') ∣ Zpos ((ggcd_step_II k a b c)₁)))
            _ _ _ (compare a b) _
          // c = Eq : g = I a
          { assume heq; refine hx }
          // c = Lt : recurse (sub b a, I a)
          { assume hlt;
            have hib : π (Zpos (I a) + Zpos (O (sub b a)) = Zpos (I b))
              { refine feq Zpos (sub_add_lt a b hlt) };
            have hzsub : π (Zpos (I z') ∣ Zpos (O (sub b a)))
              { refine div_add_cancel (Zpos (I z')) (Zpos (I a)) (Zpos (O (sub b a))) hx _;
                rewrite hib; refine hy };
            refine IHk (sub b a) (I a) (I z') (bnd_IIlt a b k hlt hbound)
                       (eucl2_I z' (sub b a) hzsub) hx }
          // c = Gt : recurse (sub a b, I b)
          { assume hgt;
            have hia : π (Zpos (I b) + Zpos (O (sub a b)) = Zpos (I a))
              { refine feq Zpos (sub_add_gt a b hgt) };
            have hzsub : π (Zpos (I z') ∣ Zpos (O (sub a b)))
              { refine div_add_cancel (Zpos (I z')) (Zpos (I b)) (Zpos (O (sub a b))) hy _;
                rewrite hia; refine hx };
            refine IHk (sub a b) (I b) (I z') (bnd_IIgt a b k hgt hbound)
                       (eucl2_I z' (sub a b) hzsub) hy }
          { reflexivity } }
        // z = O z' : even cannot divide the odd I a
        { assume z' IHz hbound hx hy; apply ⊥ₑ; refine even_div_odd_false z' a hx }
        // z = H
        { assume hbound hx hy; refine div_H_all _ } }
      // y = O b : g = gcd(I a, b)
      { assume b IH_yb;
        induction
        { assume z' IHz hbound hx hy;
          refine IHk (I a) b (I z') (bnd_IO a b k hbound) hx (eucl2_I z' b hy) }
        { assume z' IHz hbound hx hy; apply ⊥ₑ; refine even_div_odd_false z' a hx }
        { assume hbound hx hy; refine div_H_all _ } }
      // y = H : g = H
      { assume z hbound hx hy; refine hy } }
    // x = O a
    { assume a IH_xa;
      induction
      // y = I b : g = gcd(a, I b)
      { assume b IH_yb;
        induction
        { assume z' IHz hbound hx hy;
          refine IHk a (I b) (I z') (bnd_OI a b k hbound) (eucl2_I z' a hx) hy }
        { assume z' IHz hbound hx hy; apply ⊥ₑ; refine even_div_odd_false z' b hy }
        { assume hbound hx hy; refine div_H_all _ } }
      // y = O b : g = 2·gcd(a,b)
      { assume b IH_yb;
        induction
        // z = I z' (odd): z ∣ gcd(a,b) ⟹ z ∣ 2·gcd(a,b)
        { assume z' IHz hbound hx hy;
          refine div_mul_l (Zpos (I z')) (Zpos ((ggcd_fuel k a b)₁)) 2
            (IHk a b (I z') (bnd_OO a b k hbound) (eucl2_I z' a hx) (eucl2_I z' b hy)) }
        // z = O z' (even): cancel the factor 2
        { assume z' IHz hbound hx hy;
          refine mul2_div (Zpos z') (Zpos ((ggcd_fuel k a b)₁))
            (IHk a b z' (bnd_OO a b k hbound) (cancel2 (Zpos z') (Zpos a) hx)
                                              (cancel2 (Zpos z') (Zpos b) hy)) }
        { assume hbound hx hy; refine div_H_all _ } }
      // y = H : g = H
      { assume z hbound hx hy; refine hy } }
    // x = H : g = H
    { assume y z hbound hx hy; refine hx } }
end;

// ============================================================
// PHASE 2c — coprimality of the ggcd cofactors.

// add k (O w) is never 1 (it is even-or-odd ≥ 2-shaped, headed by O or I).
opaque symbol add_O_ne_H k w : π (add k (O w) ≠ H) ≔
begin
  assume k w;
  refine ind_ℙ (λ k0, add k0 (O w) ≠ H) _ _ _ k
  { assume p IHp h; refine I≠H h }
  { assume p IHp h; refine O≠H h }
  { assume h; refine I≠H h }
end;

// A positive dividing 1 is 1.
opaque symbol div_H_eq z : π (Zpos z ∣ Zpos H) → π (z = H) ≔
begin
  induction
  // z = I z'
  { assume z' IHz' h;
    apply ⊥ₑ;
    have he : π (`∃ k, H = mul (I z') k) { refine divp_elim (I z') H h };
    refine ∃ₑ he _; assume k hk;
    refine add_O_ne_H k (mul z' k) _; symmetry; refine hk }
  // z = O z'
  { assume z' IHz' h;
    apply ⊥ₑ;
    have he : π (`∃ k, H = mul (O z') k) { refine divp_elim (O z') H h };
    refine ∃ₑ he _; assume k hk;
    refine O≠H (eq_sym hk) }
  // z = H
  { assume h; reflexivity }
end;

// The two cofactors produced by ggcd_safe are coprime: any common positive
// divisor is 1. (Uses correctness x=g·aa, y=g·bb and greatest: g·z ∣ g ⟹ z ∣ 1.)
opaque symbol ggcd_cofactor_coprime x y z :
  π (Zpos z ∣ Zpos (((ggcd_safe x y)₂)₁)) →
  π (Zpos z ∣ Zpos (((ggcd_safe x y)₂)₂)) → π (z = H) ≔
begin
  assume x y z haa hbb;
  set N ≔ Stdlib.Nat.+ (size_nat x) (size_nat y);
  have hx : π (x = mul ((ggcd_fuel N x y)₁) (((ggcd_fuel N x y)₂)₁))
    { refine ∧ₑ₁ (ggcd_fuel_correct N x y) };
  have hy : π (y = mul ((ggcd_fuel N x y)₁) (((ggcd_fuel N x y)₂)₂))
    { refine ∧ₑ₂ (ggcd_fuel_correct N x y) };
  have hgzx : π (Zpos (mul ((ggcd_fuel N x y)₁) z) ∣ Zpos x)
    { refine ∃ₑ (divp_elim z (((ggcd_fuel N x y)₂)₁) haa) _; assume k hk;
      refine divp_intro (mul ((ggcd_fuel N x y)₁) z) x k _;
      rewrite mul_assoc; rewrite left hk; refine hx };
  have hgzy : π (Zpos (mul ((ggcd_fuel N x y)₁) z) ∣ Zpos y)
    { refine ∃ₑ (divp_elim z (((ggcd_fuel N x y)₂)₂) hbb) _; assume k hk;
      refine divp_intro (mul ((ggcd_fuel N x y)₁) z) y k _;
      rewrite mul_assoc; rewrite left hk; refine hy };
  have hgzg : π (Zpos (mul ((ggcd_fuel N x y)₁) z) ∣ Zpos ((ggcd_fuel N x y)₁))
    { refine ggcd_fuel_greatest N x y (mul ((ggcd_fuel N x y)₁) z)
        (Stdlib.Nat.≤_refl N) hgzx hgzy };
  refine div_H_eq z _;
  refine ∃ₑ hgzg _; assume m hm;
  refine ∃ᵢ m _; simplify;
  have key : π (Zpos ((ggcd_fuel N x y)₁) * (Zpos z * m) = Zpos ((ggcd_fuel N x y)₁) * Zpos H)
    { rewrite *_neutral; rewrite left *_assoc; symmetry; refine hm };
  have hzm : π (Zpos z * m = 1)
    { refine *_reg_r (Zpos z * m) 1 (Zpos ((ggcd_fuel N x y)₁))
        (Zpos≠Z0 ((ggcd_fuel N x y)₁)) _;
      rewrite *_com (Zpos z * m) (Zpos ((ggcd_fuel N x y)₁));
      rewrite *_com 1 (Zpos ((ggcd_fuel N x y)₁));
      refine key };
  refine eq_sym hzm
end;

// ============================================================
// PHASE 4 — uniqueness of lowest terms.
//
// Builds, on top of greatest (ggcd_fuel_greatest) and cofactor coprimality
// (ggcd_cofactor_coprime), the gcd-scaling identity gcd(k·x,k·y)=k·gcd(x,y).
// Its hard direction is the Euclid-content, discharged here WITHOUT a
// standalone Euclid's lemma: via multiplicative cancellation in divisibility
// plus cofactor coprimality. Uniqueness of lowest terms then follows.

// Generic transitivity of equality (not present in Eq.lp).
opaque symbol eq_trans [a] [x y z : τ a] : π (x = y) → π (y = z) → π (x = z) ≔
begin
  assume a x y z hxy hyz; rewrite hxy; refine hyz
end;

// ---- ℤ divisibility: scaling and cancellation of a common factor ----

// a ∣ b  ⟹  (w·a) ∣ (w·b).
opaque symbol div_scale w a b : π (a ∣ b) → π ((w * a) ∣ (w * b)) ≔
begin
  assume w a b h;
  refine ∃ₑ h _; assume k hk;
  refine ∃ᵢ k _; simplify;
  rewrite hk; rewrite *_assoc; reflexivity
end;

// w ≠ 0 and (w·a) ∣ (w·b)  ⟹  a ∣ b.
opaque symbol div_cancel_l w a b : π (w ≠ Z0) → π ((w * a) ∣ (w * b)) → π (a ∣ b) ≔
begin
  assume w a b hw h;
  refine ∃ₑ h _; assume k hk;
  refine ∃ᵢ k _; simplify;
  refine *_reg_r b (a * k) w hw _;
  rewrite *_com b w;
  rewrite hk;
  rewrite *_com w a;
  rewrite *_assoc a w k;
  rewrite *_com w k;
  rewrite left *_assoc a k w;
  reflexivity
end;

// ℙ multiplicative right-cancellation (via the Zpos·Zpos bridge + *_reg_r).
opaque symbol mul_cancel_r a b c : π (mul a c = mul b c) → π (a = b) ≔
begin
  assume a b c h;
  refine Zpos_inj a b _;
  refine *_reg_r (Zpos a) (Zpos b) (Zpos c) (Zpos≠Z0 c) _;
  refine feq Zpos h
end;

// ---- the safe gcd as a named ℙ function, with its characterizing lemmas ----

symbol gcdp : ℙ → ℙ → ℙ;
rule gcdp $x $y ↪ ((ggcd_safe $x $y)₁);

// gcd divides each argument.
opaque symbol gcdp_div_l x y : π (Zpos (gcdp x y) ∣ Zpos x) ≔
begin
  assume x y;
  refine divp_intro (gcdp x y) x (red_by_Stein_v2 x y) _;
  refine ∧ₑ₁ (ggcd_fuel_correct (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y)
end;

opaque symbol gcdp_div_r x y : π (Zpos (gcdp x y) ∣ Zpos y) ≔
begin
  assume x y;
  refine divp_intro (gcdp x y) y (((ggcd_safe x y)₂)₂) _;
  refine ∧ₑ₂ (ggcd_fuel_correct (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y)
end;

// gcd is the greatest common divisor.
opaque symbol gcdp_greatest x y z :
  π (Zpos z ∣ Zpos x) → π (Zpos z ∣ Zpos y) → π (Zpos z ∣ Zpos (gcdp x y)) ≔
begin
  assume x y z hx hy;
  refine ggcd_fuel_greatest (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y z
    (Stdlib.Nat.≤_refl (Stdlib.Nat.+ (size_nat x) (size_nat y))) hx hy
end;

// The two cofactors of (x,y) are coprime as a gcd: gcd(aa,bb) = H.
opaque symbol cofactor_gcd_H x y :
  π (gcdp (red_by_Stein_v2 x y) (((ggcd_safe x y)₂)₂) = H) ≔
begin
  assume x y;
  refine ggcd_cofactor_coprime x y
    (gcdp (red_by_Stein_v2 x y) (((ggcd_safe x y)₂)₂))
    (gcdp_div_l (red_by_Stein_v2 x y) (((ggcd_safe x y)₂)₂))
    (gcdp_div_r (red_by_Stein_v2 x y) (((ggcd_safe x y)₂)₂))
end;

// CORE: gcd(M·aa, M·bb) = M whenever aa, bb are coprime.
// This is the Euclid-content of uniqueness, proved by cancellation.
opaque symbol gcd_coprime_mul M aa bb :
  π (gcdp aa bb = H) → π (gcdp (mul M aa) (mul M bb) = M) ≔
begin
  assume M aa bb h;
  have hMaa : π (Zpos M ∣ Zpos (mul M aa))
    { refine divp_intro M (mul M aa) aa _; reflexivity };
  have hMbb : π (Zpos M ∣ Zpos (mul M bb))
    { refine divp_intro M (mul M bb) bb _; reflexivity };
  have hMG : π (Zpos M ∣ Zpos (gcdp (mul M aa) (mul M bb)))
    { refine gcdp_greatest (mul M aa) (mul M bb) M hMaa hMbb };
  refine ∃ₑ (divp_elim M (gcdp (mul M aa) (mul M bb)) hMG) _;
  assume t ht;
  have hGaa : π (Zpos (mul M t) ∣ Zpos (mul M aa))
    { rewrite left ht; refine gcdp_div_l (mul M aa) (mul M bb) };
  have hGbb : π (Zpos (mul M t) ∣ Zpos (mul M bb))
    { rewrite left ht; refine gcdp_div_r (mul M aa) (mul M bb) };
  have htaa : π (Zpos t ∣ Zpos aa)
    { refine div_cancel_l (Zpos M) (Zpos t) (Zpos aa) (Zpos≠Z0 M) hGaa };
  have htbb : π (Zpos t ∣ Zpos bb)
    { refine div_cancel_l (Zpos M) (Zpos t) (Zpos bb) (Zpos≠Z0 M) hGbb };
  have htH : π (t = H)
    { refine div_H_eq t _; rewrite left h; refine gcdp_greatest aa bb t htaa htbb };
  rewrite ht; rewrite htH; reflexivity
end;

// gcd-scaling on the cofactor decomposition (aa,bb,g abstract: no self-reference).
opaque symbol gcd_scale_abs k g aa bb :
  π (gcdp aa bb = H) →
  π (gcdp (mul k (mul g aa)) (mul k (mul g bb)) = mul k g) ≔
begin
  assume k g aa bb h;
  rewrite left mul_assoc k g aa;
  rewrite left mul_assoc k g bb;
  refine gcd_coprime_mul (mul k g) aa bb h
end;

// gcd-scaling identity: gcd(k·x, k·y) = k·gcd(x,y).
opaque symbol gcd_scale k x y : π (gcdp (mul k x) (mul k y) = mul k (gcdp x y)) ≔
begin
  assume k x y;
  have hx : π (x = mul (gcdp x y) (red_by_Stein_v2 x y))
    { refine ∧ₑ₁ (ggcd_fuel_correct (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y) };
  have hy : π (y = mul (gcdp x y) (((ggcd_safe x y)₂)₂))
    { refine ∧ₑ₂ (ggcd_fuel_correct (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y) };
  have hco : π (gcdp (red_by_Stein_v2 x y) (((ggcd_safe x y)₂)₂) = H)
    { refine cofactor_gcd_H x y };
  rewrite (feq (mul k) hx);
  rewrite (feq (mul k) hy);
  refine gcd_scale_abs k (gcdp x y) (red_by_Stein_v2 x y) (((ggcd_safe x y)₂)₂) hco
end;

// UNIQUENESS OF LOWEST TERMS (ℙ): two reduced fractions equal as a
// cross-product must coincide numerator and denominator.
//   n1·d2 = n2·d1, gcd(n1,d1)=1, gcd(n2,d2)=1  ⟹  n1 = n2 ∧ d1 = d2.
opaque symbol lowest_terms_unique n1 d1 n2 d2 :
  π (mul n1 d2 = mul n2 d1) →
  π (gcdp n1 d1 = H) → π (gcdp n2 d2 = H) →
  π (n1 = n2 ∧ d1 = d2) ≔
begin
  assume n1 d1 n2 d2 hcross hc1 hc2;
  // d2 = gcd(d2·n1, d2·d1)
  have hA : π (gcdp (mul d2 n1) (mul d2 d1) = d2)
    { rewrite (gcd_scale d2 n1 d1); rewrite hc1; reflexivity };
  // d1 = gcd(d1·n2, d1·d2)
  have hB : π (gcdp (mul d1 n2) (mul d1 d2) = d1)
    { rewrite (gcd_scale d1 n2 d2); rewrite hc2; reflexivity };
  // the two gcd inputs agree (up to commutativity and hcross)
  have ea1 : π (mul d2 n1 = mul d1 n2)
    { refine eq_trans (mul_com d2 n1) (eq_trans hcross (mul_com n2 d1)) };
  have ea2 : π (mul d2 d1 = mul d1 d2)
    { refine mul_com d2 d1 };
  have hgg : π (gcdp (mul d2 n1) (mul d2 d1) = gcdp (mul d1 n2) (mul d1 d2))
    { refine @feq2 pos pos pos gcdp (mul d2 n1) (mul d1 n2) ea1 (mul d2 d1) (mul d1 d2) ea2 };
  have hd : π (d2 = d1)
    { refine eq_trans (eq_sym hA) (eq_trans hgg hB) };
  // recover n1 = n2 by cancelling d2 in n1·d2 = n2·d1 = n2·d2
  have hn : π (n1 = n2)
    { refine mul_cancel_r n1 n2 d2
        (eq_trans hcross (feq (mul n2) (eq_sym hd))) };
  refine ∧ᵢ hn (eq_sym hd)
end;

// ---- symmetry: the second cofactor of (x,y) is the reduction of (y,x) ----
// Same fuel-alignment trick as red_by_Stein_v2_cross.
opaque symbol red_swap x y : π (((ggcd_safe x y)₂)₂ = red_by_Stein_v2 y x) ≔
begin
  assume x y;
  have hfuel : π (Stdlib.Nat.+ (size_nat y) (size_nat x) = Stdlib.Nat.+ (size_nat x) (size_nat y))
    { refine addnC (size_nat y) (size_nat x) };
  simplify;
  rewrite hfuel;
  rewrite (∧ₑ₂ (ggcd_fuel_sym (Stdlib.Nat.+ (size_nat x) (size_nat y)) y x));
  reflexivity
end;

// The reduced numerator and denominator of x/y are coprime.
opaque symbol reduced_coprime x y :
  π (gcdp (red_by_Stein_v2 x y) (red_by_Stein_v2 y x) = H) ≔
begin
  assume x y;
  rewrite left (red_swap x y);
  refine cofactor_gcd_H x y
end;

// ℙ left-cancellation and a 4-factor regrouping, for red_unique's algebra.
opaque symbol mul_cancel_l c a b : π (mul c a = mul c b) → π (a = b) ≔
begin
  assume c a b h;
  refine mul_cancel_r a b c _;
  rewrite mul_com a c; rewrite mul_com b c; refine h
end;

opaque symbol mul4_rearrange g aa h dd :
  π (mul (mul g aa) (mul h dd) = mul (mul g h) (mul aa dd)) ≔
begin
  assume g aa h dd;
  rewrite mul_assoc g aa (mul h dd);
  rewrite left mul_assoc aa h dd;
  rewrite mul_com aa h;
  rewrite mul_assoc h aa dd;
  rewrite left mul_assoc g h (mul aa dd);
  reflexivity
end;

// ℙ-LEVEL CROSS UNIQUENESS: equal positive fractions reduce identically.
//   pa·pd = pc·pb  ⟹  red(pa,pb)=red(pc,pd) ∧ red(pb,pa)=red(pd,pc).
opaque symbol red_unique pa pb pc pd :
  π (mul pa pd = mul pc pb) →
  π ((red_by_Stein_v2 pa pb = red_by_Stein_v2 pc pd)
   ∧ (red_by_Stein_v2 pb pa = red_by_Stein_v2 pd pc)) ≔
begin
  assume pa pb pc pd hcross;
  have hpa : π (pa = mul (gcdp pa pb) (red_by_Stein_v2 pa pb))
    { refine ∧ₑ₁ (ggcd_fuel_correct (Stdlib.Nat.+ (size_nat pa) (size_nat pb)) pa pb) };
  have hpb : π (pb = mul (gcdp pa pb) (red_by_Stein_v2 pb pa))
    { rewrite left (red_swap pa pb);
      refine ∧ₑ₂ (ggcd_fuel_correct (Stdlib.Nat.+ (size_nat pa) (size_nat pb)) pa pb) };
  have hpc : π (pc = mul (gcdp pc pd) (red_by_Stein_v2 pc pd))
    { refine ∧ₑ₁ (ggcd_fuel_correct (Stdlib.Nat.+ (size_nat pc) (size_nat pd)) pc pd) };
  have hpd : π (pd = mul (gcdp pc pd) (red_by_Stein_v2 pd pc))
    { rewrite left (red_swap pc pd);
      refine ∧ₑ₂ (ggcd_fuel_correct (Stdlib.Nat.+ (size_nat pc) (size_nat pd)) pc pd) };
  set g ≔ gcdp pa pb;
  set h ≔ gcdp pc pd;
  set aa ≔ red_by_Stein_v2 pa pb;
  set bb ≔ red_by_Stein_v2 pb pa;
  set cc ≔ red_by_Stein_v2 pc pd;
  set dd ≔ red_by_Stein_v2 pd pc;
  have H0 : π (mul (mul g aa) (mul h dd) = mul (mul h cc) (mul g bb))
    { refine eq_trans
        (@feq2 pos pos pos mul (mul g aa) pa (eq_sym hpa) (mul h dd) pd (eq_sym hpd))
        (eq_trans hcross
          (@feq2 pos pos pos mul pc (mul h cc) hpc pb (mul g bb) hpb)) };
  have hadcb : π (mul aa dd = mul cc bb)
    { refine mul_cancel_l (mul g h) (mul aa dd) (mul cc bb) _;
      refine eq_trans (eq_sym (mul4_rearrange g aa h dd)) (eq_trans H0 _);
      rewrite (mul4_rearrange h cc g bb);
      rewrite mul_com h g;
      reflexivity };
  refine lowest_terms_unique aa bb cc dd hadcb (reduced_coprime pa pb) (reduced_coprime pc pd)
end;