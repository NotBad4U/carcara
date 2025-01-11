/**********
The standard library use this rewrites rules in Z and Pos that has been prove confluent.

(VAR
  a: Z
  b: Z
  x : P
  q : P
  y : P
)
(RULES
  ~(Z0) -> Z0
  ~(Zpos(p)) -> Zneg(p)
  ~(Zneg(p)) -> Zpos(p)

  double(Z0) -> Z0
  double(Zpos(p)) -> Zpos(O(p))
  double(Zneg(p)) -> Zneg(O(p))

  succ_double(Z0) -> Zpos(H)
  succ_double(Zpos(p)) -> Zpos(I(p))
  succ_double(Zneg(p)) -> Zneg(pos_pred_double(p))

  pred_double(Z0) -> Zneg(H)
  pred_double(Zpos(p)) -> Zpos(pos_pred_double(p))
  pred_double(Zneg(p)) -> Zneg(I(p))

  sub(I(p), I(q)) -> double(sub(p, q))
  sub(I(p), O(q)) -> succ_double(sub(p, q))
  sub(I(p), H) -> Zpos(O(p))
  sub(O(p), I(q)) -> pred_double(sub(p, q))
  sub(O(p), O(q)) -> double(sub(p, q))
  sub(O(p), H) -> Zpos(pos_pred_double(p))
  sub(H, I(q)) -> Zneg(O(q))
  sub(H, O(q)) -> Zneg(pos_pred_double(q))
  sub(H, H) -> Z0

  +(Z0,a) -> a
  +(a,Z0) -> a
  +(Zpos(x), Zpos(y)) -> Zpos(add(x, y))
  +(Zpos(x), Zneg(y)) -> sub(x, y)
  +(Zneg(x), Zpos(y)) -> sub(y, x)
  +(Zneg(x), Zneg(y)) -> Zneg(add(x, y))

  mult(Z0, a) -> Z0
  mult(a, Z0) -> Z0
  mult(Zpos(x), Zpos(y)) -> Zpos(mul(x, y))
  mult(Zpos(x), Zneg(y)) -> Zneg(mul(x, y))
  mult(Zneg(x), Zpos(y)) -> Zneg(mul(x, y))
  mult(Zneg(x), Zneg(y)) -> Zpos(mul(x, y))


  succ(I(x)) -> O(succ(x))
  succ(O(x)) -> I(x)
  succ(H) -> O(H)
  add(I(x), I(q)) -> O(addcarry(x, q))
  add(I(x), O(q)) -> I(add(x, q))
  add(O(x), I(q)) -> I(add(x, q))
  add(O(x), O(q)) -> O(add(x, q))
  add(x, H) -> succ(x)
  add(H, y) -> succ(y)

  addcarry(I(x), I(q)) -> I(addcarry(x, q))
  addcarry(I(x), O(q)) -> O(addcarry(x, q))
  addcarry(O(x), I(q)) -> O(addcarry(x, q))
  addcarry(O(x), O(q)) -> I(add(x, q))
  addcarry(x, H) -> add(x, O(H))
  addcarry(H, y) -> add(O(H), y)

  pos_pred_double(I(x)) -> I(O(x))
  pos_pred_double(O(x)) -> I(pos_pred_double(x))
  pos_pred_double(H) -> H

  mul(I(x), y) -> add(x, O(mul(x,y)))
  mul(O(x), y) -> O(mul(x, y))
  mul(H, y) -> y
)
***********/

require open Stdlib.Bool;
require open Stdlib.Eq;
require open Stdlib.Set;
require open Stdlib.Pos;
require open Stdlib.Prop;
require open Stdlib.Comp;
require open Stdlib.Z;
require open lambdapi.Classic;
require open lambdapi.Alethe;
require open lambdapi.Ring;


rule add Z $x ↪ $x
with add $x Z ↪ $x

with add (@mul int $k $x) (mul $l $x) ↪ mul ($k + $l) $x
with add (@mul int $k $x) (add (mul $l $x) $y) ↪ add (mul ($k + $l) $x) $y

with add (@const int $x) (@const int $y) ↪ (const ($x + $y))

with mul 0 _ ↪ Z
with mul (~ ~ $k) $a ↪ mul $k $a

with mul (Zpos $x) (Zpos $y) ↪ const ((Zpos $x) × (Zpos $y))
with mul (Zpos $x) (Zneg $y) ↪ const ((Zpos $x) × (Zneg $y))
with mul (Zneg $x) (Zpos $y) ↪ const ((Zneg $x) × (Zpos $y))
with mul (Zneg $x) (Zneg $y) ↪ const ((Zneg $x) × (Zneg $y))

with mul $c (Zpos $d × $x) ↪ mul ($c × Zpos $d) $x
with mul $c (Zneg $d × $x) ↪ mul ($c × Zneg $d) $x
with mul $c (~ $x) ↪ mul (~ $c) $x
with mul $c ($x + $y) ↪ add (mul $c $x) (mul $c $y)
;

rule @const int $x ≥? @const int $y ↪ isGt ($x ≐ $y) Stdlib.Bool.or (isEq ($x ≐ $y))
with Z ≥? Z ↪ true
with Z ≥? const (Zpos _) ↪ false
with const (Zpos _) ≥? Z ↪ true
with Z ≥? const (Zneg _) ↪ true
with const (Zneg _) ≥? Z ↪ false;

rule @const int $x >? @const int $y ↪ isGt ($x ≐ $y)
with Z >? Z ↪ false
with Z >? const (Zpos _) ↪ false
with const (Zpos _) >? Z ↪ true
with const (Zneg _) >? Z ↪ true;


rule reify Z0 ↪ Z
with reify ($x + $y) ↪ add (reify $x) (reify $y)
with @reify int $a ↪ mul 1 $a
;

notation ≥ infix 10;

// Lemma Zle_not_gt n m : n <= m -> ~ n > m.
symbol Zle_not_gt n m:  πᶜ ((n ≤ m) = ¬ (n > m));

symbol Zlt_not_ge n m:  πᶜ ((n < m) = ¬ (n ≥ m));

symbol Zge_not_lt : Π n: ℤ, Π m: ℤ, πᶜ ((n ≥ m) = ¬ (n < m));

symbol Zgt_not_le : Π n: ℤ, Π m: ℤ, πᶜ ((n > m) = ¬ (n ≤ m));

// Lemma Zmult_gt_compat_r n m p : p > 0 -> n > m -> n * p > m * p.
symbol Zmult_gt_compat c a b : π (c > 0) → π (a > b) → π (c × a > c × b) ;

// Lemma Zmult_ge_compat_r n m p : n >= m -> p >= 0 -> n * p >= m * p.
symbol Zmult_ge_compat c a b : π (c > 0) → π (a ≥ b) → π (c × a ≥ c × b);

symbol Zgt_le_succ_r a b: πᶜ (a > b) → πᶜ (a ≥ b + 1);

symbol Zinv_lt a b: πᶜ (a < b) → πᶜ (~ a > ~ b);

symbol Zsum_geq_s [a b c d]: πᶜ (a ≥ b) → πᶜ (c ≥ d) → πᶜ (a + c ≥ b + d);

symbol Z_diff_geq_Z0 a b: πᶜ (a ≥ b) → πᶜ (a - b ≥ 0);
symbol Z_diff_gt_Z0 a b: πᶜ (a > b) → πᶜ (a - b > 0);


symbol ind_ℤᶜ : Π p0: (ℤ → Prop), πᶜ (p0 0) → (Π x0: ℙ, πᶜ (p0 (Zpos x0))) → (Π x0: ℙ, πᶜ (p0 (Zneg x0))) → πᶜ (`∀ᶜ x: ℤ, p0 x);

symbol ind_ℤᶜ' x : Π p0: (ℤ → Prop), πᶜ (p0 0) → (Π x0: ℙ, πᶜ (p0 (Zpos x0))) → (Π x0: ℙ, πᶜ (p0 (Zneg x0))) → πᶜ (p0 x);

opaque symbol neutral_H_× a : πᶜ (Zpos H × a = a) ≔
begin
assume a;
apply ind_ℤᶜ' a (λ u, Zpos H × u = u)
{ reflexivity }
{ reflexivity }
{ reflexivity }
end;

symbol ind_𝔹ᶜ x : Π p0: (𝔹 → Prop), πᶜ (p0 true) → πᶜ (p0 false) → πᶜ (p0 x);

opaque symbol ∨_istrueᶜ [p q] : πᶜ (istrue (p Stdlib.Bool.or q)) → πᶜ (istrue p ∨ᶜ istrue q) ≔
begin
admit
end;

print ind_Comp;

symbol ind_Compᶜ x : Π p0: (Comp → Prop), πᶜ (p0 Eq) → πᶜ (p0 Lt) → πᶜ (p0 Gt) → πᶜ (p0 x);

opaque symbol correctness_lia: πᶜ (`∀ᶜ (a: τ int), `∀ᶜ (b: τ int), istrue ((reify a) ≥? (reify b)) ⇒ᶜ a ≥ b) ≔ begin
apply ind_ℤᶜ (λ u,`∀ᶜ (b: τ int), istrue ((reify u) ≥? (reify b)) ⇒ᶜ u ≥ b)
// a = Z
{
  apply ind_ℤᶜ (λ u,istrue ((reify 0) ≥? (reify u)) ⇒ᶜ 0 ≥ u)
  { simplify; apply ⇒ᶜᵢ; assume H; apply ⇒ᶜᵢ'; assume H2; apply H2 }
  { simplify; assume HP; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H }
  { assume x; simplify; apply ⇒ᶜᵢ; assume H; apply ⇒ᶜᵢ'; assume H2; apply H2 }
}
// a = ZPos
{
  assume x;
  apply ind_ℤᶜ (λ u, istrue (reify (Zpos x) ≥? reify u) ⇒ᶜ (Zpos x ≥ u))
  // b = Z
  { apply ⇒ᶜᵢ; assume H; apply ⇒ᶜᵢ'; assume H2; apply H2 }
  // b = Zpos
  {
    assume y; simplify reify; simplify reify; simplify ≥?;
    simplify ≥;
    rewrite  neutral_H_×; rewrite  neutral_H_×;
    apply ⇒ᶜᵢ; assume H;
    have G: πᶜ (istrue (isGt (Zpos x ≐ Zpos y)) ∨ᶜ istrue (isEq (Zpos x ≐ Zpos y))) { refine @∨_istrueᶜ (isGt (Zpos x ≐ Zpos y)) (isEq (Zpos x ≐ Zpos y)) H };
    remove H;
    apply ∨ᶜₑ G
    { remove G;
      have unfold_>: πᶜ (¬ (Zpos x < Zpos y) = (¬  istrue (isLt (Zpos x ≐ Zpos y)))) { reflexivity };
      assume H;
      rewrite unfold_>;
      generalize H;
      refine @⇒ᶜₑ (istrue (isGt (Zpos x ≐ Zpos y))) (¬ (istrue (isLt (Zpos x ≐ Zpos y)))) _;
      apply ind_Compᶜ (Zpos x ≐ Zpos y) (λ u, istrue (isGt (u)) ⇒ᶜ ¬ ((istrue (isLt (u)))))
      { apply ⇒ᶜᵢ; assume H; apply  ⊥ᶜₑ H }
      { apply ⇒ᶜᵢ; assume H; apply  ⊥ᶜₑ H }
      { simplify; apply ⇒ᶜᵢ; assume H; apply ⇒ᶜᵢ'; assume H2; apply  ⊥ᶜₑ H2 };
    }
    {
      remove G;
      have unfold_>: πᶜ (¬ (Zpos x < Zpos y) = (¬  istrue (isLt (Zpos x ≐ Zpos y)))) { reflexivity };
      assume H;
      rewrite unfold_>;
      generalize H;
      refine @⇒ᶜₑ (istrue (isEq (Zpos x ≐ Zpos y))) (¬ (istrue (isLt (Zpos x ≐ Zpos y)))) _;
      apply ind_Compᶜ (Zpos x ≐ Zpos y) (λ u, istrue (isEq (u)) ⇒ᶜ ¬ ((istrue (isLt (u)))))
      { simplify; apply ⇒ᶜᵢ; assume H;   apply ⇒ᶜᵢ';  assume H'; apply  ⊥ᶜₑ H'  }
      { simplify; apply ⇒ᶜᵢ; assume H;  apply  ⊥ᶜₑ H }
      { simplify; apply ⇒ᶜᵢ; assume H;  apply  ⊥ᶜₑ H };
    }
  }
  // b = ZNeg
  {
      assume y; apply ⇒ᶜᵢ; assume H; simplify; apply ⇒ᶜᵢ'; assume H2;  apply  ⊥ᶜₑ H2
  }
}
// a = ZNeg
{
  assume x;
  apply ind_ℤᶜ (λ u, istrue (reify (Zneg x) ≥? reify u) ⇒ᶜ (Zneg x ≥ u))
  // b = Z
  { simplify; apply ⇒ᶜᵢ; assume H;  apply  ⊥ᶜₑ H }
  { assume y; apply ⇒ᶜᵢ; assume H;  apply  ⊥ᶜₑ H ;  }
  { assume y;
    simplify reify; simplify reify; simplify ≥?; simplify ≥;
    rewrite  neutral_H_×; rewrite  neutral_H_×;
    apply ⇒ᶜᵢ; assume H;
    have G: πᶜ (istrue (isGt (Zneg x ≐ Zneg y)) ∨ᶜ istrue (isEq (Zneg x ≐ Zneg y))) { refine @∨_istrueᶜ (isGt (Zneg x ≐ Zneg y)) (isEq (Zneg x ≐ Zneg y)) H };
    remove H;
    apply ∨ᶜₑ G
    {
      remove G;
      have unfold_>: πᶜ (¬ (Zneg x < Zneg y) = (¬  istrue (isLt (Zneg x ≐ Zneg y)))) { reflexivity };
      assume H;
      rewrite unfold_>;
      generalize H;
      refine @⇒ᶜₑ (istrue (isGt (Zneg x ≐ Zneg y))) (¬ (istrue (isLt (Zneg x ≐ Zneg y)))) _;
      apply ind_Compᶜ (Zneg x ≐ Zneg y) (λ u, istrue (isGt (u)) ⇒ᶜ ¬ ((istrue (isLt (u)))))
      { simplify;  apply ⇒ᶜᵢ; assume H;  apply  ⊥ᶜₑ H }
      { simplify;  apply ⇒ᶜᵢ; assume H;  apply  ⊥ᶜₑ H }
      { simplify;  apply ⇒ᶜᵢ; assume H;  apply ⇒ᶜᵢ'; assume H2;  apply  ⊥ᶜₑ H2 }
    }
    {
      remove G;
      assume H;
      have unfold_>: πᶜ (¬ (Zneg x < Zneg y) = (¬  istrue (isLt (Zneg x ≐ Zneg y)))) { reflexivity };
      rewrite unfold_>;
      remove unfold_>;
      generalize H;
      refine @⇒ᶜₑ (istrue (isEq (Zneg x ≐ Zneg y))) (¬ (istrue (isLt (Zneg x ≐ Zneg y)))) _;
      apply ind_Compᶜ (Zneg x ≐ Zneg y) (λ u, istrue (isEq (u)) ⇒ᶜ ¬ ((istrue (isLt (u)))))
      { simplify;  apply ⇒ᶜᵢ; assume H;  apply ⇒ᶜᵢ'; assume H2;  apply  ⊥ᶜₑ H2  }
      { apply ⇒ᶜᵢ; assume H;  apply  ⊥ᶜₑ H }
      {  apply ⇒ᶜᵢ; assume H;  apply  ⊥ᶜₑ H }
    }
  }
}
end;

opaque symbol completude_lia2: πᶜ (`∀ᶜ (a: τ int), `∀ᶜ (b: τ int), (a ≥ b)  ⇒ᶜ istrue ((reify a) ≥? (reify b))) ≔ begin
  apply ind_ℤᶜ (λ u,  `∀ᶜ b, (u ≥ b) ⇒ᶜ istrue (reify u ≥? reify b))
  // a = Z
  {
    apply ind_ℤᶜ (λ u,  (0 ≥ u) ⇒ᶜ istrue (reify 0 ≥? reify u))
    // b = Z
    {  apply ⇒ᶜᵢ; assume H;  apply trivial }
    // b = Zpos
    { assume y; simplify; apply ⇒ᶜᵢ; assume H; refine ⇒ᶜₑ' H trivial;  }
    // b = Zneg
    { assume y; simplify; apply ⇒ᶜᵢ; assume H; apply trivial }
  }
  // a = Zpos
  {
    assume x;
    apply ind_ℤᶜ (λ u,  (Zpos x ≥ u) ⇒ᶜ istrue (reify (Zpos x) ≥? reify u))
    // b = Z
    { simplify; apply ⇒ᶜᵢ; assume H; apply trivial }
    // b = Zpos
    {
        assume y; simplify reify; simplify reify;
        simplify ≥?; simplify ≥; simplify;
        apply ind_Compᶜ (compare_acc x Eq y) (λ u, (istrue (isLt (u)) ⇒ ⊥) ⇒ᶜ istrue (isGt (u) Stdlib.Bool.or isEq (u)))
        { apply ⇒ᶜᵢ; assume H; apply trivial }
        { simplify;  apply ⇒ᶜᵢ; assume H; refine ⇒ᶜₑ' H trivial;   }
        { simplify;  apply ⇒ᶜᵢ; assume H; apply trivial }
    }
    // b = Zneg
    { assume y; simplify reify; simplify reify; simplify; apply ⇒ᶜᵢ; assume H; apply trivial  }
  }
  // a = Zneg
  {
    assume x;
    apply ind_ℤᶜ (λ u,  (Zneg x ≥ u) ⇒ᶜ istrue (reify (Zneg x) ≥? reify u))
    { simplify; apply ⇒ᶜᵢ; assume H; refine ⇒ᶜₑ' H trivial;  }
    { assume y; simplify;  apply ⇒ᶜᵢ; assume H; refine ⇒ᶜₑ' H trivial;  }
    {
        assume y; simplify;
        apply ind_Compᶜ (compare_acc y Eq x) (λ u, (istrue (isLt (u)) ⇒ ⊥) ⇒ᶜ istrue (isGt (u) Stdlib.Bool.or isEq (u)))
        { apply ⇒ᶜᵢ; assume H; apply trivial }
        { simplify; apply ⇒ᶜᵢ; assume H; refine ⇒ᶜₑ' H trivial; }
        { simplify; apply ⇒ᶜᵢ; assume H; apply trivial }
    }
  }
end;

symbol completude_lia a b: πᶜ (a ≥ b) → πᶜ (istrue ((reify a) ≥? (reify b))) ≔
begin
  assume a b Ha_ge_b; refine (⇒ᶜₑ (∀ᶜₑ b (∀ᶜₑ a completude_lia2)) Ha_ge_b);
end;

symbol Zgt_le_succ_r_eq a b: πᶜ ((a > b) = (a ≥ b + 1));

symbol Zinv_lt_eq a b: πᶜ ((a < b) = (~ a > ~ b));

symbol Zinv_le_eq a b: πᶜ ((a ≤ b) = (~ a ≥ ~ b));

symbol Z_diff_geq_Z0_eq a b: πᶜ ((a ≥ b) = (a - b ≥ 0));

symbol Z_diff_gt_Z0_eq a b: πᶜ ((a > b) = (a - b > 0));

symbol Z_diff_eq_Z0_eq a b: πᶜ ((a = b) = (a - b = 0));


//symbol Z_eq_antisym [a b: τ int]: πᶜ (a = b) → πᶜ ((a ≤ b) ∧ᶜ (a ≥ b));

//Axioms
symbol Z_eq_antisym (a b: τ int):  πᶜ ((¬ (a = b)) = ¬ (a ≥ b));

symbol Zmult_eq_compat_eq (c a b: τ int) : πᶜ ((¬ (a = b)) = ¬ (c × a = c × b));
symbol Zmult_gt_compat_eq c a b : πᶜ (¬ (a > b) = ¬ (c × a > c × b)) ;
symbol Zmult_ge_compat_eq c a b : πᶜ (¬ (a ≥ b) = ¬ (c × a ≥ c × b)) ;

opaque >;
opaque <;

// Example =========
symbol F: τ int;

opaque symbol lia_example : π̇ ((¬ ((~ 1) × F = (~ 1 × 10)) ∨ᶜ ¬ (F < 5) ∨ᶜ ((~ 1 × F) + F < (~ 1 × 10) + 5)) ⟇ ▩) ≔
begin
apply ∨ᶜᵢ₁;
// step 1
rewrite .[x in _ ∨ᶜ _ ∨ᶜ x ] Zlt_not_ge ;
// step 2
rewrite Zinv_lt_eq;
// step 3
rewrite Z_diff_geq_Z0_eq;
rewrite Z_diff_gt_Z0_eq;
// step 4
rewrite Zgt_le_succ_r_eq;
// step 5
rewrite (Zmult_eq_compat_eq (~ 1) (~ 1 × F) (~ 1 × 10));
rewrite (Zmult_ge_compat_eq 1 (~ F - ~ 5) (0 + 1));
rewrite (Zmult_ge_compat_eq 1 (((~ 1 × F) + F) - ((~ 1 × 10) + 5)) 0);
rewrite Z_eq_antisym;
//step 2
rewrite imp_eq_or;
apply ⇒ᶜᵢ; assume H1;
rewrite imp_eq_or;
apply ⇒ᶜᵢ; assume H2;
apply ¬ᶜᵢ; assume H3;
set H1l ≔ (~ 1 × (~ 1 × F));
set H1r ≔ (~ 1 × (~ 1 × 10));
set H2l ≔ (1 × (~ F - ~ 5));
set H2r ≔ ((0 + 1));
set H3l ≔ (1 × (((~ 1 × F) + F) - ((~ 1 × 10) + 5)));
set H3r ≔ (0);
//step 5
have Hsum: πᶜ (H1l + H2l + H3l ≥ H1r + H2r + H3r) {
    apply Zsum_geq_s (Zsum_geq_s H1 H2) H3;
};
refine @completude_lia (H1l + H2l + H3l) (H1r + H2r + H3r)  Hsum;
end;


opaque symbol lia_example2 : π̇ (¬ ((~ 1) × F = (~ 1 × 10)) ⟇ ¬ (F < 5) ⟇ ((~ 1 × F) + F < (~ 1 × 10) + 5) ⟇ ▩) ≔
begin
  simplify;
  rewrite or_identity_r;
  apply π̇ₗ lia_example
end;