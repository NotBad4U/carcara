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
  —(Z0) -> Z0
  —(Zpos(p)) -> Zneg(p)
  —(Zneg(p)) -> Zpos(p)
  —(—(a)) -> a

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

require open Stdlib.Pos Stdlib.Nat Stdlib.Z Stdlib.Set Stdlib.Prop Stdlib.Eq Stdlib.Bool Stdlib.Comp Stdlib.List;
require open lambdapi.Classic;
require open lambdapi.Alethe;
require open lambdapi.Ring;

notation ≥ infix 10;

constant symbol R : TYPE;
constant symbol ring: Set;
rule τ ring ↪ R;

constant symbol cst: ℤ → R;

symbol var : ℤ → ℤ → R;
/* semantics: [var k x] = k * x
note that the second argument could be any type that has a ring structure
(we then would take R : TYPE → TYPE) */
symbol opp:R → R;
right associative commutative symbol add:R → R → R;
symbol mul: ℤ → R → R;

symbol R_ind: Π p: (R → Prop), 
  (Π x0: ℤ, πᶜ ( p (cst x0))) →
  (Π x0: R, πᶜ ( p (opp x0))) →
  (Π x0: ℤ, Π y0: ℤ, πᶜ (p (var x0 y0))) →
  (Π x0: R, Π y0: R, πᶜ (p (add x0 y0))) →
  (Π x0: ℤ, Π y0: R, πᶜ (p (mul x0 y0))) →
  πᶜ (`∀ᶜ x: R, p x);

rule var _ 0 ↪ cst 0;

rule opp (var $x $k) ↪ var $x (— $k)
with opp (cst $k) ↪ cst (— $k)
with opp (opp $x) ↪ $x
with opp (add $x $y) ↪ add (opp $x) (opp $y);
// // // note that opp is totally defined on terms built with var, cst, opp and add, i.e. no normal form contains opp
rule add (var $x $k) (var $x $l) ↪ var $x ($k + $l)
with add (var $x $k) (add (var $x $l) $y) ↪ add (var $x ($k + $l)) $y
with add (cst $k) (cst $l) ↪ cst ($k + $l)
with add (cst $k) (add (cst $l) $y) ↪ add (cst ($k + $l)) $y
with add (cst 0) $x ↪ $x
with add $x (cst 0) ↪ $x;

//multiplication by a constant (optional)

rule mul $k (var $z $l) ↪ var $z ($k * $l)
with mul $k (opp $r) ↪ mul (— $k) $r
with mul $k (add $r $s) ↪ add (mul $k $r) (mul $k $s)
with mul $k (cst $z) ↪ cst ($k * $z)
with mul $k (mul $l $z) ↪ mul ($k * $l) $z;
// // note that mul is totally defined on terms built from var, cst, opp, add and mul, i.e. no normal form contains mul

// // reification
// // WARNING: this symbol is declared as sequential
// // and the reduction relation is not stable by substitution
sequential symbol reify : ℤ → R;
rule reify 0 ↪ cst 0
with reify (Zpos $x) ↪ cst (Zpos $x)
with reify (Zneg $x) ↪ cst (Zneg $x)
with reify (— $x) ↪ opp (reify $x)
with reify ($x + $y) ↪ add (reify $x) (reify $y)

with reify (0 * $y) ↪ mul 0 (reify $y)
with reify (Zpos $x * $y) ↪ mul (Zpos $x) (reify $y)
with reify (Zneg $x * $y) ↪ mul (Zneg $x) (reify $y)
with reify ($y * 0) ↪ mul 0 (reify $y)
with reify ($y * Zpos $x) ↪ mul (Zpos $x) (reify $y)
with reify ($y * Zneg $x) ↪ mul (Zneg $x) (reify $y)

with reify $x ↪ var $x 1; // must be the last rule for reify


// eval function
symbol denote: R → ℤ;
rule denote (var $k $i) ↪ $k * $i
with denote (cst $k) ↪ $k
with denote (opp $x) ↪ — (denote $x)
with denote (add $x $y) ↪ (denote $x) + (denote $y)
;

// Lemma Zle_not_gt n m : n <= m -> — n > m.
symbol Zle_not_gt n m:  πᶜ ((n ≤ m) = ¬ (n > m));

symbol Zlt_not_ge n m:  πᶜ ((n < m) = ¬ (n ≥ m));

symbol Zge_not_lt : Π n: ℤ, Π m: ℤ, πᶜ ((n ≥ m) = ¬ (n < m));

symbol Zgt_not_le : Π n: ℤ, Π m: ℤ, πᶜ ((n > m) = ¬ (n ≤ m));

// Lemma Zmult_gt_compat_r n m p : p > 0 -> n > m -> n * p > m * p.
symbol Zmult_gt_compat c a b : π (c > 0) → π (a > b) → π (c * a > c * b) ;

// Lemma Zmult_ge_compat_r n m p : n >= m -> p >= 0 -> n * p >= m * p.
symbol Zmult_ge_compat c a b : π (c > 0) → π (a ≥ b) → π (c * a ≥ c * b);

symbol Zgt_le_succ_r a b: πᶜ (a > b) → πᶜ (a ≥ b + 1);

symbol Zinv_lt a b: πᶜ (a < b) → πᶜ (— a > — b);

symbol Zsum_geq_s a b c d : πᶜ (a ≥ b) → πᶜ (c ≥ d) → πᶜ (a + c ≥ b + d);

symbol Z_diff_geq_Z0 a b: πᶜ (a ≥ b) → πᶜ (a - b ≥ 0);
symbol Z_diff_gt_Z0 a b: πᶜ (a > b) → πᶜ (a - b > 0);



symbol ind_ℤᶜ' x : Π p0: (ℤ → Prop), πᶜ (p0 0) → (Π x0: ℙ, πᶜ (p0 (Zpos x0))) → (Π x0: ℙ, πᶜ (p0 (Zneg x0))) → πᶜ (p0 x);

opaque symbol neutral_H_* a : πᶜ (Zpos H * a = a) ≔
begin
assume a;
apply ind_ℤᶜ' a (λ u, Zpos H * u = u)
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

symbol Zgt_le_succ_r_eq a b: πᶜ ((a > b) = (a ≥ b + 1));

symbol Zinv_lt_eq a b: πᶜ ((a < b) = (— a > — b));

symbol Zinv_le_eq a b: πᶜ ((a ≤ b) = (— a ≥ — b));

symbol Z_diff_geq_Z0_eq a b: πᶜ ((a ≥ b) = (a - b ≥ 0));

symbol Z_diff_gt_Z0_eq a b: πᶜ ((a > b) = (a - b > 0));

symbol Z_diff_eq_Z0_eq a b: πᶜ ((a = b) = (a - b = 0));


//Axioms
symbol Z_eq_antisym (a b: τ int):  πᶜ ((¬ (a = b)) = ¬ (a ≥ b));

symbol Zmult_eq_compat_eq (c a b: τ int) : πᶜ ((¬ (a = b)) = ¬ (c * a = c * b));
symbol Zmult_gt_compat_eq c a b : πᶜ (¬ (a > b) = ¬ (c * a > c * b)) ;
symbol Zmult_ge_compat_eq c a b : πᶜ (¬ (a ≥ b) = ¬ (c * a ≥ c * b)) ;

symbol la_mult_neg_eq [t1 t2 t3] : πᶜ ((t1 < 0) ⇒ᶜ (t2 = t3) ⇒ᶜ (t1 * t2) = (t1 * t3)) ≔
begin
assume t1 t2 t3; apply ⇒ᶜᵢ; assume H; apply ⇒ᶜᵢ; assume H2; rewrite H2; reflexivity
end;

//FIXME: give proof
symbol la_mult_neg_lt t1 t2 t3 : πᶜ (t1 < 0) → πᶜ (t2 < t3) → πᶜ ((t1 * t2) > (t1 * t3));
symbol la_mult_neg_leq [t1 t2 t3] : πᶜ ((t1 < 0) ⇒ᶜ (t2 ≤ t3) ⇒ᶜ (t1 * t2) ≥ (t1 * t3));
symbol la_mult_neg_gt [t1 t2 t3] : πᶜ ((t1 < 0) ⇒ᶜ (t2 > t3) ⇒ᶜ (t1 * t2) < (t1 * t3));
symbol la_mult_neg_ge [t1 t2 t3] : πᶜ ((t1 < 0) ⇒ᶜ (t2 ≥ t3) ⇒ᶜ (t1 * t2) ≤ (t1 * t3));


symbol ind_ℤᶜ : Π p0: (ℤ → Prop), πᶜ (p0 0) → (Π x0: ℙ, πᶜ (p0 (Zpos x0))) → (Π x0: ℙ, πᶜ (p0 (Zneg x0))) → πᶜ (`∀ᶜ x, p0 x);

opaque symbol inj : πᶜ (`∀ᶜ x, (denote (reify x)) = x) ≔ begin
apply ind_ℤᶜ (λ u,  (denote (reify u)) = u)
{reflexivity}
{reflexivity}
{reflexivity}
end;


sequential symbol =R: R → R → τ bool; notation =R infix 10;
rule (var $x $c1) =R (var $x $c2) ↪ isEq ($c1 ≐ $c2)
with (var $x $c1) =R (var $y $c2) ↪ false
with (var $x $c1) =R add _ _ ↪ false
with (var $x $c1) =R mul _ _ ↪ false
with (var $x $c1) =R cst _ ↪ false
with (var $x $c1) =R opp _ ↪ false
with add $x1 $y1 =R add $x2 $y2 ↪ ($x1 =R $x2) Stdlib.Bool.and ($y1 =R $y2)
with add _ _ =R mul _ _ ↪ false
with add _ _ =R cst _ ↪ false
with add _ _ =R var _ _ ↪ false
with add _ _ =R opp _ ↪ false
with (mul $x1 $y1) =R (mul $x2 $y2) ↪ (isEq ($x1 ≐ $x2)) Stdlib.Bool.and ($y1 =R $y2)
with mul _ _ =R add _ _ ↪ false
with mul _ _ =R cst _ ↪ false
with mul _ _ =R var _ _ ↪ false
with mul _ _ =R opp _ ↪ false
with cst $x =R cst $y ↪ isEq ($x ≐ $y)
with cst _ =R mul _ _ ↪ false
with cst _ =R add _ _ ↪ false
with cst _ =R opp _ ↪ false
with cst _ =R var _ _ ↪ false
with opp $x =R opp $y ↪ ($x =R $y)
with opp _ =R mul _ _ ↪ false
with opp _ =R add _ _ ↪ false
with opp _ =R cst _ ↪ false
with opp _ =R var _ _ ↪ false
;

sequential symbol >R: R → R → τ bool; notation >R infix 20;
rule (var $x $c1) >R (var $x $c2) ↪ isGt ($c1 ≐ $c2)
with (var $x $c1) >R (var $y $c2) ↪ false
with (var $x $c1) >R add _ _ ↪ false
with (var $x $c1) >R mul _ _ ↪ false
with (var $x $c1) >R cst _ ↪ false
with (var $x $c1) >R opp _ ↪ false
with add $x1 $y1 >R add $x2 $y2 ↪ ($x1 >R $x2) Stdlib.Bool.and ($y1 >R $y2)
with add _ _ >R mul _ _ ↪ false
with add _ _ >R cst _ ↪ false
with add _ _ >R var _ _ ↪ false
with add _ _ >R opp _ ↪ false
with (mul $x1 $y1) >R (mul $x2 $y2) ↪ (isGt ($x1 ≐ $x2)) Stdlib.Bool.and ($y1 >R $y2)
with mul _ _ >R add _ _ ↪ false
with mul _ _ >R cst _ ↪ false
with mul _ _ >R var _ _ ↪ false
with mul _ _ >R opp _ ↪ false
with cst $x >R cst $y ↪ isGt ($x ≐ $y)
with cst _ >R mul _ _ ↪ false
with cst _ >R add _ _ ↪ false
with cst _ >R opp _ ↪ false
with cst _ >R var _ _ ↪ false
with opp $x >R opp $y ↪ ($x >R $y)
with opp _ >R mul _ _ ↪ false
with opp _ >R add _ _ ↪ false
with opp _ >R cst _ ↪ false
with opp _ >R var _ _ ↪ false
;

symbol ≥R ≔ λ x, λ y,  (x =R y) Stdlib.Bool.or (x >R y);

opaque symbol Radd_correct : πᶜ (`∀ᶜ (x : R), `∀ᶜ (y : R), denote (add x y) = denote x + denote y) ≔ begin
  apply ∀ᶜᵢ; assume x; apply ∀ᶜᵢ; assume y; reflexivity
end;

opaque symbol Ropp_correct : πᶜ (`∀ᶜ (x : R), `∀ᶜ (y : R), denote (opp x) = — denote x) ≔ begin
  apply ∀ᶜᵢ; assume x; apply ∀ᶜᵢ; assume y; reflexivity
end;

// opaque symbol RMul_correct : πᶜ (`∀ᶜ (x : R), `∀ᶜ (y : R), denote (mul x y) = denote x * denote y) ≔ begin
//   apply ∀ᶜᵢ; assume x; apply ∀ᶜᵢ; assume y; reflexivity
// end;

// opaque symbol eq_subst : πᶜ (`∀ᶜ (x : ℤ), `∀ᶜ (y : ℤ), istrue (isEq (x ≐ y)) ⇒ᶜ x = y) ≔
// begin
// apply ind_ℤᶜ (λ u, `∀ᶜ (y : ℤ), istrue (isEq (u ≐ y)) ⇒ᶜ u = y)
// {
//   apply ind_ℤᶜ (λ u, istrue (isEq (0 ≐ u)) ⇒ᶜ 0 = u)
//   {apply ⇒ᶜᵢ; assume H; reflexivity }
//   { assume x; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H }
//   { assume x; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H }
// }
// {
//   assume p;
//   apply ind_ℤᶜ (λ u, istrue (isEq (Zpos p ≐ u)) ⇒ᶜ Zpos p = u)
//   { apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H }
//   {
//     assume q; simplify;
//   }
//   {}
// }
// {}
// end;

opaque symbol correct_liaAC : πᶜ (`∀ᶜ (x : R), `∀ᶜ (y : R), istrue (x =R y) ⇒ᶜ denote x = denote y) ≔ begin
apply R_ind (λ u, `∀ᶜ (y : R), istrue (u =R y) ⇒ᶜ denote u = denote y)
{
  assume c1;
  apply R_ind (λ u, istrue (cst c1 =R u) ⇒ᶜ denote (cst c1) = denote u)
  { assume c2; simplify isEq; apply ⇒ᶜᵢ; assume H; simplify; admit  } //CASE
  { simplify; assume x; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H }
  { simplify; assume x y; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H }
  { simplify; assume x y; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H }
  { simplify; assume x y; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H }
}
{
  assume x;
  apply R_ind (λ u, istrue (opp x =R u) ⇒ᶜ denote (opp x) = denote u)
  { assume c2; simplify; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H }
  { assume y; simplify =R;  apply ⇒ᶜᵢ; assume H; admit } //CASE
  { simplify; assume c y; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H }
  { simplify; assume c y; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H }
  { simplify; assume c y; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H }
}
{
  assume c1 x;
  apply R_ind (λ u, istrue (var c1 x =R u) ⇒ᶜ denote (var c1 x) = denote u)
  { assume c2; simplify; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H }
  { assume y; simplify =R;  apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H } 
  { assume c2 y; apply ⇒ᶜᵢ;  assume H; apply ⊥ᶜₑ H } //CASE
  { simplify; assume c y; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H }
  { simplify; assume c y; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H }
}
{
  assume x1 y1;
  apply R_ind (λ u, istrue (add x1 y1 =R u) ⇒ᶜ denote (add x1 y1) = denote u)
  {assume c2; simplify; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H}
  {assume x; simplify; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H}
  {assume c2 y; simplify; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H}
  { assume x2 y2; apply ⇒ᶜᵢ; assume H;  admit } //CASE
  { assume c2 y2; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H}
}
{
  assume c1 x;
  apply R_ind (λ u, istrue (mul c1 x =R u) ⇒ᶜ denote (mul c1 x) = denote u)
  {assume c2; simplify; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H}
  {assume y; simplify; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H}
  {assume c2 y; simplify; apply ⇒ᶜᵢ; assume H; apply ⊥ᶜₑ H}
  { assume x2 y2; apply ⇒ᶜᵢ; assume H;  apply ⊥ᶜₑ H } 
  { assume c2 y2; apply ⇒ᶜᵢ; simplify; assume H; admit} //CASE
};
end;
