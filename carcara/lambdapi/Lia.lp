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

notation ≥ infix 10;

constant symbol R : TYPE;

constant symbol cst:ℤ → R;

symbol var : ℤ → ℕ → R;
/* semantics: [var k x] = k * x
note that the second argument could be any type that has a ring structure
(we then would take R : TYPE → TYPE) */
symbol opp:R → R;
symbol add:R → R → R;
symbol mul:ℤ → R → R;


symbol R_ind: Π p: (R → Prop), 
  (Π x0: ℤ, πᶜ ( p (cst x0))) →
  (Π x0: R, πᶜ ( p (opp x0))) →
  (Π x0: ℤ, Π y0: ℕ, πᶜ (p (var x0 y0))) →
  (Π x0: R, Π y0: R, πᶜ (p (add x0 y0))) →
  (Π x0: ℤ, Π y0: R, πᶜ (p (mul x0 y0))) →
  Π x: R, πᶜ (p x);

symbol mif : 𝔹 → R → R → R;

rule mif true  $x _ ↪ $x
with mif false _ $y ↪ $y;

symbol addnorm: R → R → R;

// norm
rule addnorm (var $k $i) (var $l $j) ↪ mif ($i Stdlib.Nat.≤ $j)
                                        (add (var $k $i) (var $l $j))
                                        (add (var $l $j) (var $k $i))

with addnorm (add (var $c1 $i) $xs) (add (var $c2 $j) $ys) ↪
    mif ($i Stdlib.Nat.≤ $j)
        (add (var $c1 $i) (addnorm $xs (add (var $c2 $j) $ys)))
    // else
        (add (var $c2 $j) (addnorm (add (var $c1 $i) $xs) $ys))

with addnorm (add (var $c1 $i) $xs) (var $c2 $j) ↪
    mif ($i Stdlib.Nat.≤ $j)
    (add (var $c1 $i) (addnorm $xs (var $c2 $j)))
    // else
    (add (var $c2 $j) (addnorm (var $c1 $i) $xs))

with addnorm (var $c1 $i) (add (var $c2 $j) $ys) ↪
    mif ($i Stdlib.Nat.≤ $j)
        (add (var $c1 $i) (addnorm (var $c2 $j) $ys))
    // else
        (add (var $c2 $j) (addnorm (var $c1 $i) $ys))
with addnorm (var $c1 $i) (add (cst $k) $tl) ↪ add (cst $k) (addnorm (var $c1 $i) $tl)
with addnorm (cst $c1) (cst $c2) ↪  (cst ($c1 + $c2))
with addnorm (cst $c) (var $k $i) ↪  add (cst $c) (var $k $i)
with addnorm (var $k $i) (cst $c) ↪  add (cst $c) (var $k $i)
with addnorm (add (cst $x) $xs) (add (cst $a) $ys) ↪ add (cst ($x + $a)) (addnorm $xs $ys)
with addnorm (cst $x) (add (cst $a) $tl) ↪ addnorm (cst ($x + $a)) $tl
with addnorm (add $x $xs) (cst $c) ↪ add (cst $c) (addnorm $x $xs)

with addnorm (add (var $k $i) $xs) (add (cst $c) $ys) ↪
    (add (cst $c) (addnorm (add (var $k $i) $xs) $ys))
with addnorm (add (cst $c) $xs) (add (var $k $i) $ys) ↪
    (add (cst $c) (addnorm $xs (add (var $k $i) $ys)))
with addnorm (add (cst $c1) $y) (add (cst $c2) $b) ↪
    (add (cst ($c1 + $c2)) (addnorm $y $b))                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 


with addnorm (var $c1 $i) (add (var $c2 $j) $tl) ↪
    mif ($i Stdlib.Nat.≤ $j)
        (add (var $c1 $i) (addnorm (var $c2 $j) $tl))
        (add (var $c2 $j) (addnorm (var $c1 $i) $tl))

with addnorm (add $x $xs) (addnorm $y $ys) ↪ addnorm (add $x $xs) (add $y $ys)

with addnorm (add $x $xs) (var $c $y) ↪ addnorm $x (add (var $c $y) $xs)
;


rule var 0 _ ↪ cst 0;
rule opp (var $k $x) ↪ var (— $k) $x
with opp (cst $k) ↪ cst (— $k)
with opp (opp $x) ↪ $x
with opp (add $x $y) ↪ add (opp $x) (opp $y);
// // // note that opp is totally defined on terms built with var, cst, opp and add, i.e. no normal form contains opp
rule add (var $c1 $i) (var $c2 $i) ↪ (var ($c1 + $c2) $i)
with add (var $c1 $i) (add (var $c2 $i) $y) ↪ (add (var ($c1 + $c2) $i) $y)
with add (cst $k) (cst $l) ↪ cst ($k + $l)
with add (cst $k) (add (cst $l) $y) ↪ add (cst ($k + $l)) $y
with add (cst 0) $x ↪ $x
with add $x (cst 0) ↪ $x
;


//multiplication by a constant (optional)
rule mul $k (var $l $i) ↪ var ($k * $l) $i
with mul $k (opp $r) ↪ mul (— $k) $r
with mul $k (add $x $y) ↪ add (mul $k $x) (mul $k $y)
with mul $k (cst $c) ↪ cst ($k * $c)
with mul $k (mul $l $z) ↪ mul ($k * $l) $z;
// // note that mul is totally defined on terms built from var, cst, opp, add and mul, i.e. no normal form contains mul

// // reification
// // WARNING: this symbol is declared as sequential
// // and the reduction relation is not stable by substitution

sequential symbol get_env' : 𝕃 int → ℤ → 𝕃 int;
rule get_env' $l (Zpos _) ↪ $l
with get_env' $l (Zneg _) ↪ $l
with get_env' $l Z0 ↪ $l
with get_env' $l ($x + $y) ↪ (get_env' $l $x) Stdlib.List.++ (get_env' $l $y)
with get_env' $l ($x * $y) ↪ (get_env' $l $x) Stdlib.List.++ (get_env' $l $y)
with get_env' $l (— $x) ↪ get_env' $l $x
with get_env' $l $x ↪ $x ⸬ $l
;

symbol get_env : ℤ → 𝕃 int ≔  λ (f: ℤ), get_env' Stdlib.List.□ f;


sequential symbol eqℤ: τ int → τ int → 𝔹;
rule eqℤ $x $x ↪ true
with eqℤ $x $y ↪ false;

sequential symbol reify : 𝕃 int →  ℤ → R;
rule reify $env 0 ↪ cst 0
with reify $env (Zpos $x) ↪ cst (Zpos $x)
with reify $env (Zneg $x) ↪ cst (Zneg $x)
with reify $env (— $x) ↪ opp (reify $env $x)
with reify $env ($x + $y) ↪ addnorm (reify $env $x) (reify $env $y)

with reify $env (0 * $y) ↪ mul 0 (reify $env $y)
with reify $env (Zpos $x * $y) ↪ mul (Zpos $x) (reify $env $y)
with reify $env (Zneg $x * $y) ↪ mul (Zneg $x) (reify $env $y)
with reify $env ($y * 0) ↪ mul 0 (reify $env $y)
with reify $env ($y * Zpos $x) ↪ mul (Zpos $x) (reify $env $y)
with reify $env ($y * Zneg $x) ↪ mul (Zneg $x) (reify $env $y)

with reify $env $x ↪ var 1 (index (eqℤ) $x $env); // must be the last rule for reify

// For debug
symbol not_found: τ int;

// eval function
symbol denote: 𝕃 int → R → ℤ;
rule denote $env (var $k $i) ↪ $k * (nth not_found $env $i)
with denote _ (cst $k) ↪ $k
with denote $env (opp $x) ↪ — (denote $env $x)
with denote $env (add $x $y) ↪ (denote $env $x) + (denote $env $y)
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


symbol ind_ℤᶜ : Π p0: (ℤ → Prop), πᶜ (p0 0) → (Π x0: ℙ, πᶜ (p0 (Zpos x0))) → (Π x0: ℙ, πᶜ (p0 (Zneg x0))) → πᶜ (`∀ᶜ x: ℤ, p0 x);

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


//symbol Z_eq_antisym [a b: τ int]: πᶜ (a = b) → πᶜ ((a ≤ b) ∧ᶜ (a ≥ b));

//Axioms
symbol Z_eq_antisym (a b: τ int):  πᶜ ((¬ (a = b)) = ¬ (a ≥ b));

symbol Zmult_eq_compat_eq (c a b: τ int) : πᶜ ((¬ (a = b)) = ¬ (c * a = c * b));
symbol Zmult_gt_compat_eq c a b : πᶜ (¬ (a > b) = ¬ (c * a > c * b)) ;
symbol Zmult_ge_compat_eq c a b : πᶜ (¬ (a ≥ b) = ¬ (c * a ≥ c * b)) ;


// print ℙ;

symbol ind_ℙᶜ : Π p0: (ℙ → Prop), 
  (Π x0: ℙ, πᶜ (p0 x0) →
  πᶜ (p0 (I x0))) →
  (Π x0: ℙ, πᶜ (p0 x0) →
  πᶜ (p0 (O x0))) →
  πᶜ (p0 H) →
  πᶜ (`∀ᶜ x, p0 x);

opaque symbol opp_idem c : πᶜ (Stdlib.Comp.opp (Stdlib.Comp.opp c) = c) ≔
begin
  assume c;
  apply ind_Compᶜ c (λ u, Stdlib.Comp.opp (Stdlib.Comp.opp u) = u)
  { reflexivity; } { reflexivity; } { reflexivity; }
end;

symbol compare_acc_com:
  πᶜ (`∀ᶜ x, `∀ᶜ y, `∀ᶜ c, compare_acc y c x = Stdlib.Comp.opp (compare_acc x (Stdlib.Comp.opp c) y)) ≔
begin
  apply ind_ℙᶜ (λ u, `∀ᶜ y, `∀ᶜ c, compare_acc y c u = Stdlib.Comp.opp (compare_acc u (Stdlib.Comp.opp c) y))
  // case I
  { assume x xrec;
    apply ind_ℙᶜ (λ u, `∀ᶜ c, compare_acc u c (I x) = Stdlib.Comp.opp (compare_acc (I x) (Stdlib.Comp.opp c) u))
     { assume y IH; apply ∀ᶜᵢ; assume c; simplify; rewrite (∀ᶜₑ c (∀ᶜₑ y xrec)); reflexivity; }
     { assume y IH; apply ∀ᶜᵢ; assume c; simplify; rewrite (∀ᶜₑ Lt (∀ᶜₑ y xrec)); reflexivity; }
     { apply ∀ᶜᵢ; assume c; reflexivity; } }
  // case O
  { assume x xrec;
    apply ind_ℙᶜ (λ u, `∀ᶜ c, compare_acc u c (O x) = Stdlib.Comp.opp (compare_acc (O x) (Stdlib.Comp.opp c) u))
     { assume y IH; apply ∀ᶜᵢ; assume c; simplify; rewrite (∀ᶜₑ Gt (∀ᶜₑ y xrec)); reflexivity; }
     { assume y IH; apply ∀ᶜᵢ; assume c; simplify; rewrite (∀ᶜₑ c (∀ᶜₑ y xrec)); reflexivity; }
     { apply ∀ᶜᵢ; assume c; reflexivity; } }
  // case H
  { apply ind_ℙᶜ (λ u, `∀ᶜ c, compare_acc u c H = Stdlib.Comp.opp (compare_acc H (Stdlib.Comp.opp c) u))
     { assume y IH; apply ∀ᶜᵢ; assume c; reflexivity; }
     { assume y IH; apply ∀ᶜᵢ; assume c; reflexivity; }
     { apply ∀ᶜᵢ; assume c; simplify; symmetry; rewrite opp_idem; reflexivity; } }
end;

symbol ≐_com : πᶜ (`∀ᶜ (x: τ int), `∀ᶜ (y: τ int), (x ≐ y) = Stdlib.Comp.opp (y ≐ x)) ≔
begin
//    admit
  apply ind_ℤᶜ (λ u, `∀ᶜ y, u ≐ y = Stdlib.Comp.opp (y ≐ u))
  // case Z0
  { apply ind_ℤᶜ (λ u, 0 ≐ u = Stdlib.Comp.opp (u ≐ 0)) 
    { reflexivity; } { reflexivity; } { reflexivity; }
  }
  // case Zpos
  { assume x;
    apply ind_ℤᶜ (λ u, Zpos x ≐ u = Stdlib.Comp.opp (u ≐ Zpos x)) 
     { reflexivity; }
     { assume y; simplify; rewrite (∀ᶜₑ Eq (∀ᶜₑ x (∀ᶜₑ y compare_acc_com))); reflexivity; }
     { reflexivity; } }
  // case Zneg
  { assume x;
  apply ind_ℤᶜ (λ u, Zneg x ≐ u = Stdlib.Comp.opp (u ≐ Zneg x)) 
     { reflexivity; }
     { reflexivity; }
     { assume y; simplify; rewrite (∀ᶜₑ Eq (∀ᶜₑ y (∀ᶜₑ x compare_acc_com))); reflexivity; } }
end;

symbol ≐_decides: Π x: τ int, Π y: τ int, πᶜ (((x ≐ y) = Eq)) → πᶜ (x = y);

symbol ind_Comp2ᶜ : Π p0: (Comp → Prop), πᶜ (p0 Eq) → πᶜ (p0 Lt) → πᶜ (p0 Gt) → Π x,  πᶜ (p0 x);

symbol ≤_antisymᶜ [x y] : πᶜ ((x ≤ y) ⇒ᶜ (y ≤ x) ⇒ᶜ x = y) ≔
begin
  assume x y;
    have e : πᶜ (¬ (istrue(isGt (x ≐ y))) ⇒ᶜ ¬ (istrue(isGt (y ≐ x))) ⇒ᶜ x = y)
    { rewrite (∀ᶜₑ y (∀ᶜₑ x ≐_com)) };
    print ind_Compᶜ;
    print ⇒ᶜₑ;
    refine (@⇒ᶜₑ ((y ≐ x) = (y ≐ x)) (¬ (istrue (isGt (Stdlib.Comp.opp (y ≐ x)))) ⇒ᶜ (¬ (istrue (isGt (y ≐ x))) ⇒ᶜ (x = y)))) _ _
    {
        refine ind_Comp2ᶜ (λ c, ((y ≐ x) = c)  ⇒ᶜ ¬ (istrue(isGt (Stdlib.Comp.opp c))) ⇒ᶜ ¬ (istrue(isGt c)) ⇒ᶜ x = y) _ _ _ (y ≐ x)
        { apply ⇒ᶜᵢ;  assume H; apply ⇒ᶜᵢ; assume h1; apply ⇒ᶜᵢ; assume h2; symmetry; refine ≐_decides y x H }
        { simplify; apply ⇒ᶜᵢ;  assume h1; apply ⇒ᶜᵢ; assume f; apply ⇒ᶜᵢ; assume H2; apply ⊥ᶜₑ;  refine ⇒ᶜₑ' (f ) trivial; }
        { simplify; apply ⇒ᶜᵢ;  assume h1; apply ⇒ᶜᵢ; assume f; apply ⇒ᶜᵢ; assume H2; apply ⊥ᶜₑ;  refine ⇒ᶜₑ' (H2) trivial; }
    }
    {reflexivity};
    refine e
end;

opaque symbol la_disequality [t1 t2] : πᶜ ((t1 = t2) ∨ᶜ ¬ (t1 ≤ t2) ∨ᶜ ¬ (t2 ≤ t1)) ≔
begin
    assume t1 t2;
    rewrite or_com;
    rewrite left ∨ᶜ_assoc_eq;
    rewrite imp_eq_or;
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ; assume H;
    apply ⇒ᶜᵢ; assume H2;
    apply  ⇒ᶜₑ (⇒ᶜₑ (@≤_antisymᶜ t1 t2) H);
    apply H2;
end;

opaque symbol la_totality [t1 t2] : πᶜ ((t1 ≤ t2) ∨ᶜ (t2 ≤ t1)) ≔
begin
    assume t1 t2;
    simplify;
    rewrite (∀ᶜₑ t1 (∀ᶜₑ t2 ≐_com));
    refine ind_Comp2ᶜ (λ c, (istrue (isGt c) ⇒ ⊥) ∨ᶜ (istrue (isGt (Stdlib.Comp.opp c)) ⇒ ⊥)) _ _ _ (t1 ≐ t2)
    { apply ∨ᶜᵢ₁; simplify; apply ⇒ᶜᵢ'; refine (λ x, x) }
    { apply ∨ᶜᵢ₁; simplify; apply ⇒ᶜᵢ'; refine (λ x, x) }
    { apply ∨ᶜᵢ₂; simplify; apply ⇒ᶜᵢ'; refine (λ x, x) }
end;

opaque symbol ≤_compat_addᶜ  : πᶜ (`∀ᶜ x, `∀ᶜ y, `∀ᶜ a, (x ≤ y) ⇒ᶜ x + a ≤ y + a) ≔
begin
  refine IL_imp_Cl2 _ _;
  assume x;
  refine IL_imp_Cl3 _ _;
  assume y;
  refine IL_imp_Cl3 _ _;
  assume a;
  apply ⇒ᶜ_in_IL;
  refine ≤_compat_add x y a;
end;

opaque symbol >_to_≥ x y: πᶜ ((x > y) ⇒ᶜ (x ≥ y)) ≔
begin
    assume x y; simplify;
    refine ind_Comp2ᶜ (λ c, ((istrue (isGt (c)) ⇒ ⊥) ⇒ ⊥) ⇒ᶜ (istrue (isLt (c)) ⇒ ⊥)) _ _ _ (x ≐ y)
    { apply ⇒ᶜᵢ; assume H; apply ⇒ᶜᵢ'; refine (λ x, x) }
    {
      apply ⇒ᶜᵢ; assume H; apply ⇒ᶜᵢ'; assume H2;
      apply ⇒ᶜₑ' H; apply ⇒ᶜᵢ'; refine (λ x, x)
    }
    { apply ⇒ᶜᵢ; assume H; apply ⇒ᶜᵢ'; refine (λ x, x) } 
end;

opaque symbol ≐_subᶜ : πᶜ (`∀ᶜ x, `∀ᶜ y,  (x ≐ y) = (x + — y ≐ Z0)) ≔
begin
refine IL_imp_Cl2 _ _;
assume x;
refine IL_imp_Cl3 _ _;
assume y;
refine ≐_sub x y
end;

opaque symbol ≤_compat_mult x y a : πᶜ (0 < a) → πᶜ ((x < y) ⇒ᶜ x * a < y * a) ≔
begin
    assume x y a HageqZ; 
    simplify;
    admit
end;


opaque symbol ≤_reflᶜ x : πᶜ (x ≤ x) ≔
begin
    assume x; 
    refine ⇒ᶜₑ (≤_compat_addᶜ Z0 Z0 x) _;
    apply ⇒ᶜᵢ';
    refine (λ x, x);
end;

opaque symbol la_rw_eq [t u] : πᶜ ((t = u) = (t ≤ u) ∧ᶜ (u ≤ t)) ≔
begin
assume t u;
apply prop_ext;
apply ∧ᶜᵢ
{
    apply ⇒ᶜᵢ; assume Heq; rewrite Heq;
    apply ∧ᶜᵢ { refine ≤_reflᶜ u } {  refine ≤_reflᶜ u};
}
{
    apply ⇒ᶜᵢ;
    assume H;
    refine ⇒ᶜₑ (⇒ᶜₑ (@≤_antisymᶜ t u) _) _
    { refine ∧ᶜₑ₁ H }
    { refine ∧ᶜₑ₂ H };
};
end;

opaque symbol la_mult_neg_eq [t1 t2 t3] : πᶜ ((t1 < 0) ⇒ᶜ (t2 = t3) ⇒ᶜ (t1 * t2) = (t1 * t3)) ≔
begin
assume t1 t2 t3; apply ⇒ᶜᵢ; assume H; apply ⇒ᶜᵢ; assume H2; rewrite H2; reflexivity
end;

//FIXME: give proof
symbol la_mult_neg_lt t1 t2 t3 : πᶜ (t1 < 0) → πᶜ (t2 < t3) → πᶜ ((t1 * t2) > (t1 * t3));
symbol la_mult_neg_leq [t1 t2 t3] : πᶜ ((t1 < 0) ⇒ᶜ (t2 ≤ t3) ⇒ᶜ (t1 * t2) ≥ (t1 * t3));
symbol la_mult_neg_gt [t1 t2 t3] : πᶜ ((t1 < 0) ⇒ᶜ (t2 > t3) ⇒ᶜ (t1 * t2) < (t1 * t3));
symbol la_mult_neg_ge [t1 t2 t3] : πᶜ ((t1 < 0) ⇒ᶜ (t2 ≥ t3) ⇒ᶜ (t1 * t2) ≤ (t1 * t3));


symbol inj (σ: 𝕃 int) : Π x: ℤ, πᶜ ((denote σ (reify σ x)) = x);

symbol inj2 (σ: 𝕃 int) : πᶜ (`∀ᶜ x: ℤ, (denote σ (reify σ x)) = x) ≔
begin
assume σ;
apply ind_ℤᶜ (λ u, (denote σ (reify σ u)) = u)
{reflexivity}
{reflexivity}
{reflexivity}
end;


// Example =========
// opaque symbol lia_example (F: τ int) : π̇ (¬ ((— 1) * F = (— 1 * 10)) ⟇ ¬ (F < 5) ⟇ ((— 1 * F) + F < (— 1 * 10) + 5) ⟇ ▩) ≔
// begin
//   set H1l ≔ (— 1) * F;
//   set H1r ≔ (— 1 * 10);
//   set H2l ≔ F;
//   set H2r ≔ 5;
//   set H3l ≔ (— 1 * F) + F;
//   set H3r ≔ (— 1 * 10) + 5;
//   have Hlia: π̇ ((¬ (H1l = H1r) ∨ᶜ ¬ (H2l < H2r) ∨ᶜ (H3l < H3r)) ⟇ ▩) {
//     apply ∨ᶜᵢ₁;
//     rewrite .[x in _ ∨ᶜ _ ∨ᶜ x ] Zlt_not_ge;
//     rewrite Zinv_lt_eq;
//     rewrite Z_diff_geq_Z0_eq;
//     rewrite Z_diff_gt_Z0_eq;
//     rewrite Zgt_le_succ_r_eq;
//     rewrite (Zmult_eq_compat_eq (— 1) H1l H1r);
//     rewrite (Zmult_ge_compat_eq 1 (— H2l - — H2r) (0 + 1));
//     rewrite (Zmult_ge_compat_eq 1 (H3l - H3r) 0);
//     rewrite Z_eq_antisym;
//     rewrite imp_eq_or;
//     apply ⇒ᶜᵢ; assume H1;
//     rewrite imp_eq_or;
//     apply ⇒ᶜᵢ; assume H2;
//     apply ¬ᶜᵢ; assume H3;
//     set H1l' ≔ (— 1 * H1l);
//     set H1r' ≔ (— 1 * H1r);
//     set H2l' ≔ (1 * (— H2l - — H2r));
//     set H2r' ≔ (1 * (0 + 1));
//     set H3l' ≔ (1 * (H3l - H3r));
//     set H3r' ≔ 0;
//     set σ ≔ get_env (H1l' + H2l' + H3l'); 
//     have contra: πᶜ ((denote σ (reify σ (H1l' + H2l' + H3l'))) ≥ (denote σ (reify σ (H1r' + H2r' + H3r')))) {
//       rewrite inj;
//       rewrite inj;
//       apply (Zsum_geq_s H1l' H1r' (H2l' + H3l') (H2r' + H3r')  H1 (Zsum_geq_s H2l' H2r' H3l' H3r' H2 H3));
//     };
//     apply ⇒ᶜₑ' contra;
//     apply trivial;
//   };
//   simplify;
//   rewrite or_identity_r;
//   apply π̇ₗ Hlia;
// end;
