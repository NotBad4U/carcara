require Stdlib.Nat as Nat;
require open Stdlib.ExtraRules Stdlib.Z Stdlib.List Stdlib.PropExt Stdlib.Classic Stdlib.Impred;

// alethe.core's `iff_equiv_eq`, which the ℤ lemmas below need before core is
// opened (further down, where the la_* rules start). Distinct name, because
// protected symbols are still opened and would shadow core's in importers.
protected opaque symbol iff_equiv_eq' x y : π ((x ⇔ y) = (x = y)) ≔
begin
  assume x y;
  refine propExt (x ⇔ y) (x = y) _ _
  { assume H; refine propExt x y _ _ { assume Hx; refine ∧ₑ₁ H Hx } { assume Hy; refine ∧ₑ₂ H Hy } }
  { assume Hxeqy; rewrite Hxeqy; apply Stdlib.Prop.⇔_refl }
end;

inductive G: TYPE ≔
| Cst: ℤ → G
| Var: ℕ → ℤ → G
;

constant symbol grp : Set;
rule τ grp ↪ G;

// multiplication by a constant
symbol mul: ℤ → 𝕃 grp → 𝕃 grp;

rule mul $k ((Cst $l) ⸬ $xs) ↪ Cst ($k * $l) ⸬ (mul $k $xs)
with mul $k ((Var $i $l) ⸬ $xs) ↪ Var $i ($k * $l) ⸬ (mul $k $xs)
with mul _ □ ↪ □;

// opposite
symbol opp ≔ mul (— 1);


/* evaluation of an arithmetic expression wrt a list of values for variables

variables with indexes not in the list are interpreted by 0 */

symbol nth ≔ nth 0;

symbol val_grp: τ grp →  𝕃 int → ℤ;
rule val_grp (Cst $k) _ ↪ $k
with val_grp (Var $i $k) $l ↪ (nth $l $i) * $k;

symbol val: τ(list grp × list int) → ℤ;

rule val (□ ‚ _) ↪ 0
with val (($x ⸬ $xs) ‚ $l) ↪ (val_grp $x $l) + (val ($xs ‚ $l));

symbol va l x ≔ val (x ‚ l);


constant symbol R : TYPE;
constant symbol Index : ℕ → R;
constant symbol New : ℕ → R;

symbol case [a] : R → (ℕ → τ a) → (ℕ → τ a) → τ a;

rule case (Index $i) $f _ ↪ $f $i
with case (New $i) _ $g ↪ $g $i;

/* index of a value in a list: returns New if the value is not
definitionally equivalent to some element of the list */

sequential symbol index: ℕ → Π [a], τ a → τ(list a) → R;

rule index $k _ □ ↪ New $k
with index $k $x ($x ⸬ _) ↪ Index $k
with index $k $x ($y ⸬ $l) ↪ index ($k +1) $x $l;

/* reification: given a Lambdapi term x of type ℤ, compute an
expression in G and a list of values whose evaluation is equal to
x. WARNING: rfy is sequential. */

sequential symbol rfy: τ(list int) → ℤ → τ(list grp × list int);

// addition
rule rfy $l ($x + $y) ↪
  let x ≔ rfy $l $x in let y ≔ rfy (x ₂) $y in ((x ₁) ++ (y ₁)) ‚ (y ₂)

// opposite
with rfy $l (— $x) ↪ let x ≔ rfy $l $x in opp (x ₁) ‚ (x ₂)

// substraction
with rfy $l ($x - $y) ↪ rfy $l ($x + — $y)

// constants
with rfy $l 0 ↪ (Cst 0 ⸬ □) ‚ $l
with rfy $l (Zpos $k) ↪ (Cst (Zpos $k) ⸬ □) ‚ $l
with rfy $l (Zneg $k) ↪ (Cst (Zneg $k) ⸬ □) ‚ $l

// multiplication by a constant
with rfy $l (0 * _) ↪ (Cst 0 ⸬ □) ‚ $l
with rfy $l (Zpos $k * $x) ↪ let x ≔ rfy $l $x in (mul (Zpos $k) (x ₁)) ‚ (x ₂)
with rfy $l (Zneg $k * $x) ↪ let x ≔ rfy $l $x in (mul (Zneg $k) (x ₁)) ‚ (x ₂)
with rfy $l ($x * Zpos $k) ↪ let x ≔ rfy $l $x in (mul (Zpos $k) (x ₁)) ‚ (x ₂)
with rfy $l ($x * Zneg $k) ↪ let x ≔ rfy $l $x in (mul (Zneg $k) (x ₁)) ‚ (x ₂)

//other cases are abstracted by a variable
with rfy $l $x ↪
  case (index _0 $x $l) (λ i, (Var i 1 ⸬ □) ‚ $l) (λ i, (Var i 1 ⸬ □) ‚ ($l ++ ($x ⸬ □)))
;

symbol reify ≔ rfy □;

symbol compN : ℕ → ℕ → Comp;

rule compN _0 _0 ↪ Eq
with compN _0 (_ +1) ↪ Lt
with compN (_ +1) _0 ↪ Gt
with compN ($x +1) ($y +1) ↪ compN $x $y;

symbol leG : τ grp → τ grp → 𝔹;
rule leG (Cst _) _ ↪ true
with leG (Var _ _) (Cst _) ↪ false
with leG (Var $i _) (Var $j _) ↪ $i Nat.≤ $j;

opaque symbol +_left_comm a b c : π (a + (b + c) = b + (a + c)) ≔
begin
  assume a b c; rewrite left +_assoc a b c; rewrite +_com a b; refine +_assoc b a c
end;

opaque symbol ++_eq_+ l x y : π (val ((x ++ y) ‚ l) =  val (x ‚ l) + val (y ‚ l)) ≔
begin
assume l;
induction
{
  assume y;
  reflexivity
}
{
  assume x xs ih;
  simplify;
  assume y;
  rewrite ih y;
  rewrite +_assoc;
  reflexivity
}
end;

opaque symbol compN_correct x y : π (compN x y = Eq ⇒ x = y) ≔
begin
induction
{ induction
  {assume h; reflexivity}
  {assume y hy h; apply ⊥ₑ; apply Lt≠Eq h}
}
{ assume x hx; induction
  {assume h; apply ⊥ₑ; apply Gt≠Eq h}
  {assume y hy h; apply feq (+1); apply hx y h }
}
end;

opaque symbol split_correct l g : π (val ((split g ₁) ‚ l) + val ((split g ₂) ‚ l) = val (g ‚ l)) ≔
begin
  assume l;
  refine ind_𝕃2 (λ g, val ((split g ₁) ‚ l) + val ((split g ₂) ‚ l) = val (g ‚ l)) _ _ _
  { reflexivity }
  { assume x; refine +Z0 (val ((x ⸬ □) ‚ l)) }
  { assume x y g ih;
    change π ((val_grp x l + val ((split g ₁) ‚ l)) + (val_grp y l + val ((split g ₂) ‚ l))
              = val_grp x l + (val_grp y l + val (g ‚ l)));
    rewrite left ih;
    rewrite +_assoc (val_grp x l) (val ((split g ₁) ‚ l)) (val_grp y l + val ((split g ₂) ‚ l));
    rewrite +_left_comm (val ((split g ₁) ‚ l)) (val_grp y l) (val ((split g ₂) ‚ l));
    reflexivity }
end;

opaque symbol merge_correct l (le : τ grp → τ grp → 𝔹) g1 g2 :
  π (val ((merge le g1 g2) ‚ l) = val (g1 ‚ l) + val (g2 ‚ l)) ≔
begin
  assume l le;
  induction
  { assume g2; reflexivity }
  { assume x xs ih;
    induction
    { symmetry; refine +Z0 (val ((x ⸬ xs) ‚ l)) }
    { assume y ys ih2;
      refine ind_𝔹 (λ b, val ((if b (x ⸬ merge le xs (y ⸬ ys)) (y ⸬ merge le (x ⸬ xs) ys)) ‚ l)
                         = val ((x ⸬ xs) ‚ l) + val ((y ⸬ ys) ‚ l)) _ _ (le x y)
      { change π (val_grp x l + val ((merge le xs (y ⸬ ys)) ‚ l)
                  = (val_grp x l + val (xs ‚ l)) + val ((y ⸬ ys) ‚ l));
        rewrite ih (y ⸬ ys);
        symmetry; refine +_assoc (val_grp x l) (val (xs ‚ l)) (val ((y ⸬ ys) ‚ l)) }
      { change π (val_grp y l + val ((merge le (x ⸬ xs) ys) ‚ l)
                  = val ((x ⸬ xs) ‚ l) + (val_grp y l + val (ys ‚ l)));
        rewrite ih2;
        refine +_left_comm (val_grp y l) (val ((x ⸬ xs) ‚ l)) (val (ys ‚ l)) } } }
end;

opaque symbol mergesort_correct l (le : τ grp → τ grp → 𝔹) g :
  π (val ((mergesort le g) ‚ l) = val (g ‚ l)) ≔
begin
  assume l le;
  refine ind_𝕃_size (λ g, val ((mergesort le g) ‚ l) = val (g ‚ l)) _;
  refine case_𝕃2
    (λ g, (`∀ g' : τ (list grp), istrue (size g' Nat.< size g)
             ⇒ val ((mergesort le g') ‚ l) = val (g' ‚ l))
          ⇒ val ((mergesort le g) ‚ l) = val (g ‚ l)) _ _ _
  { assume rec; reflexivity }
  { assume x rec; reflexivity }
  { assume x y g rec;
    change π (val ((merge le (mergesort le (x ⸬ (split g ₁))) (mergesort le (y ⸬ (split g ₂)))) ‚ l)
              = val ((x ⸬ y ⸬ g) ‚ l));
    rewrite merge_correct l le (mergesort le (x ⸬ (split g ₁))) (mergesort le (y ⸬ (split g ₂)));
    rewrite rec (x ⸬ (split g ₁)) (size_split1 g);
    rewrite rec (y ⸬ (split g ₂)) (size_split2 g);
    refine split_correct l (x ⸬ y ⸬ g) }
end;

symbol collect_from : τ grp → 𝕃 grp → 𝕃 grp;
rule collect_from $x □ ↪ $x ⸬ □
with collect_from (Cst $c1) (Cst $c2 ⸬ $l) ↪ collect_from (Cst ($c1 + $c2)) $l
with collect_from (Cst $c) (Var $j $k ⸬ $l) ↪ Cst $c ⸬ collect_from (Var $j $k) $l
with collect_from (Var $i $k) (Cst $c ⸬ $l) ↪ Var $i $k ⸬ collect_from (Cst $c) $l
with collect_from (Var $i $k1) (Var $j $k2 ⸬ $l) ↪
    case_Comp (compN $i $j)
        (collect_from (Var $i ($k1 + $k2)) $l)
        (Var $i $k1 ⸬ collect_from (Var $j $k2) $l)
        (Var $i $k1 ⸬ collect_from (Var $j $k2) $l);

symbol collect : 𝕃 grp → 𝕃 grp;
rule collect □ ↪ □
with collect ($x ⸬ $l) ↪ collect_from $x $l;

opaque symbol collect_from_correct l g x : π (val ((collect_from x g) ‚ l) = val_grp x l + val (g ‚ l)) ≔
begin
  assume l;
  induction
  { assume x; reflexivity }
  { induction
    { assume c2 g ih;
      induction
      { assume c1;
        change π (val ((collect_from (Cst (c1 + c2)) g) ‚ l) = c1 + (c2 + val (g ‚ l)));
        rewrite ih (Cst (c1 + c2));
        refine +_assoc c1 c2 (val (g ‚ l)) }
      { assume i k;
        change π (val_grp (Var i k) l + val ((collect_from (Cst c2) g) ‚ l)
                  = val_grp (Var i k) l + val (((Cst c2) ⸬ g) ‚ l));
        rewrite ih (Cst c2); reflexivity } }
    { assume j k2 g ih;
      induction
      { assume c;
        change π (c + val ((collect_from (Var j k2) g) ‚ l) = c + val (((Var j k2) ⸬ g) ‚ l));
        rewrite ih (Var j k2); reflexivity }
      { assume i k1;
        refine ind_Comp (λ u, compN i j = u ⇒ val ((case_Comp u (collect_from (Var i (k1 + k2)) g) (Var i k1 ⸬ collect_from (Var j k2) g) (Var i k1 ⸬ collect_from (Var j k2) g)) ‚ l) = val_grp (Var i k1) l + val (((Var j k2) ⸬ g) ‚ l)) _ _ _ (compN i j) _
        // same variable
        { assume heq; rewrite compN_correct i j heq;
          change π (val ((collect_from (Var j (k1 + k2)) g) ‚ l)
                    = (nth l j * k1) + ((nth l j * k2) + val (g ‚ l)));
          rewrite ih (Var j (k1 + k2));
          change π ((nth l j * (k1 + k2)) + val (g ‚ l)
                    = (nth l j * k1) + ((nth l j * k2) + val (g ‚ l)));
          rewrite *_distr_l (nth l j) k1 k2;
          refine +_assoc (nth l j * k1) (nth l j * k2) (val (g ‚ l)) }
        { assume h;
          change π (val_grp (Var i k1) l + val ((collect_from (Var j k2) g) ‚ l)
                    = val_grp (Var i k1) l + val (((Var j k2) ⸬ g) ‚ l));
          rewrite ih (Var j k2); reflexivity }
        { assume h;
          change π (val_grp (Var i k1) l + val ((collect_from (Var j k2) g) ‚ l)
                    = val_grp (Var i k1) l + val (((Var j k2) ⸬ g) ‚ l));
          rewrite ih (Var j k2); reflexivity }
        { reflexivity } } } }
end;

opaque symbol collect_correct l g : π (val ((collect g) ‚ l) = val (g ‚ l)) ≔
begin
  assume l;
  induction
  { reflexivity }
  { assume x g ih; refine collect_from_correct l g x }
end;

symbol remove0 : τ(list grp) → τ(list grp);

rule remove0 □ ↪ □
with remove0 (Cst 0 ⸬ $l) ↪ remove0 $l
with remove0 (Cst (Zpos $k) ⸬ $l) ↪ Cst (Zpos $k) ⸬ remove0 $l
with remove0 (Cst (Zneg $k) ⸬ $l) ↪ Cst (Zneg $k) ⸬ remove0 $l
with remove0 (Var _ 0 ⸬ $l) ↪ remove0 $l
with remove0 (Var $i (Zpos $k) ⸬ $l) ↪ Var $i (Zpos $k) ⸬ remove0 $l
with remove0 (Var $i (Zneg $k) ⸬ $l) ↪ Var $i (Zneg $k) ⸬ remove0 $l
;

opaque symbol remove0_correct l gs : π (val ((remove0 gs) ‚ l) = val (gs ‚ l)) ≔
begin
  assume l;
  induction // on l
  {
    reflexivity
  }
  {
    induction // on g
    {
      // Case Cst k
      induction 
      // Case Z0
      { assume  gs ih;  simplify; apply ih }
      // Case Zpos
      { assume c gs ih; simplify; rewrite ih; reflexivity }
      // Case Zneg
      { assume c gs ih; simplify;  rewrite ih; reflexivity }
    }
    {
      // Case Var i k
      assume i;
      induction // on k
      {assume gs ih; simplify; rewrite ih; reflexivity} // Case Z0
      { assume c gs ih; simplify; rewrite ih; reflexivity } // Case Zpos
      { assume c gs ih; simplify; rewrite ih; reflexivity } // Case Zneg
    }
  }
end;

symbol norm_speed x ≔ remove0 (collect (mergesort leG x));

symbol varmax : 𝕃 grp → ℕ;

rule varmax ((Cst _) ⸬ $xs) ↪ (varmax $xs)
with varmax ((Var $k _) ⸬ $xs) ↪ max $k (varmax $xs)
with varmax □ ↪ _0;

opaque symbol eq_trans [a] (x y z:τ a) : π(x = y ⇒ y = z ⇒ x = z) ≔
begin
assume a x y z xy yz; rewrite xy; refine yz
end;

opaque symbol norm_correct (x: 𝕃 grp) l : π(val((norm_speed x) ‚ l) = val(x ‚ l)) ≔
begin
  assume x l;
  change π (val ((remove0 (collect (mergesort leG x))) ‚ l) = val (x ‚ l));
  rewrite remove0_correct l (collect (mergesort leG x));
  rewrite collect_correct l (mergesort leG x);
  refine mergesort_correct l leG x
end;

symbol ≐_decides_neq [x y] : π (x ≐ y ≠ Eq ⇒ x ≠ y) ≔
begin
assume x y h h2;
apply h;
rewrite h2;
remove h; remove h2; remove x;
generalize y;
induction
{reflexivity}
{
  induction
  {assume x ih; simplify; rewrite left .[x in _ = x] ih; simplify; reflexivity }
  {assume x ih; simplify; rewrite left .[x in _ = x] ih; simplify; reflexivity }
  {reflexivity}
}
{
  induction
  {assume x ih; simplify; rewrite left .[x in _ = x] ih; simplify; reflexivity }
  {assume x ih; simplify; rewrite left .[x in _ = x] ih; simplify; reflexivity }
  {reflexivity}
}
end;

opaque symbol reify_correct x: π(val(reify x) = x) ≔
begin
induction
{reflexivity}
{reflexivity}
{reflexivity}
end;

opaque symbol reify_correct_withenv l x: π(val(rfy l x) = x) ≔
begin
assume l;
induction
{reflexivity}
{reflexivity}
{reflexivity}
end;

opaque symbol poly_norm_eq (a b : τ int) :
  π (val (norm_speed (reify a ₁) ‚ (reify a ₂))
     = val (norm_speed (rfy (reify a ₂) b ₁) ‚ (rfy (reify a ₂) b ₂)))
  → π (a = b) ≔
begin
  assume a b h;
  rewrite left .[x in x = _] reify_correct a;
  rewrite .[x in val x = _] prodExt (reify a);
  rewrite left .[x in _ = x] reify_correct_withenv (reify a ₂) b;
  rewrite .[x in _ = val x] prodExt (rfy (reify a ₂) b);
  rewrite left .[x in x = _] norm_correct (reify a ₁) (reify a ₂);
  rewrite left .[x in _ = x] norm_correct (rfy (reify a ₂) b ₁) (rfy (reify a ₂) b ₂);
  refine h
end;

symbol ≤_eq_¬_> n m:  π ((n ≤ m) = ¬ (n > m)) ≔
begin
assume n m;
rewrite left iff_equiv_eq';
apply ∧ᵢ
{
  simplify;
  assume h;
  change π (¬ ¬ ¬ istrue (isGt (n ≐ m)));
  rewrite ¬¬ₑ_eq;
  refine h
}
{
  simplify;
  assume h1 h2;
  apply h1;
  change π (¬ ¬ istrue (isGt (n ≐ m)));
  rewrite ¬¬ₑ_eq;
  refine h2
}
end;

symbol <_eq_¬_≥ n m:  π ((n < m) = ¬ (n ≥ m)) ≔
begin
  assume n m;
  simplify ≥;
  simplify rule off;
  rewrite ¬¬ₑ_eq;
  reflexivity
end;

symbol ≥_eq_¬_< : Π n: ℤ, Π m: ℤ, π ((n ≥ m) = ¬ (n < m)) ≔
begin
  assume n m;
  simplify ≥;
  simplify rule off;
  reflexivity
end;

symbol >_eq_¬_≤ : Π n: ℤ, Π m: ℤ, π ((n > m) = ¬ (n ≤ m)) ≔
begin
  assume n m;
  simplify ≤;
  simplify rule off;
  reflexivity
end;

opaque symbol >_compat_mul_pos_l c a b : π (c > 0) → π (a > b) → π (c * a > c * b) ≔
begin
  induction
  { assume a b hc; apply ⊥ₑ; refine >_irrefl 0 hc }
  { assume p a b hc hab;
    rewrite *_com (Zpos p) a; rewrite *_com (Zpos p) b;
    refine ∧ₑ₁ (>_compat_mul a b p) hab }
  { assume p a b hc; apply ⊥ₑ; refine hc (λ h, h) }
end;

opaque symbol ≥_compat_mul_pos_l c a b : π (c > 0) → π (a ≥ b) → π (c * a ≥ c * b) ≔
begin
  induction
  { assume a b hc; apply ⊥ₑ; refine >_irrefl 0 hc }
  { assume p a b hc hab;
    rewrite *_com (Zpos p) a; rewrite *_com (Zpos p) b;
    refine ∧ₑ₁ (≥_compat_mul a b p) hab }
  { assume p a b hc; apply ⊥ₑ; refine hc (λ h, h) }
end;

opaque symbol ≥_add_≥ a b c d : π (a ≥ b) → π (c ≥ d) → π (a + c ≥ b + d) ≔
begin
  assume a b c d hab hcd;
  have h1 : π (b + d ≤ a + d) { refine ≤_compat_add b a d (∧ₑ₁ (≥_≤ a b) hab) };
  have h2 : π (a + d ≤ a + c)
  { rewrite +_com a d; rewrite +_com a c; refine ≤_compat_add d c a (∧ₑ₁ (≥_≤ c d) hcd) };
  refine ∧ₑ₂ (≥_≤ (a + c) (b + d)) (≤_trans (b + d) (a + d) (a + c) h1 h2)
end;

opaque symbol <_opp_eq a b: π ((a < b) = (— a > — b)) ≔
begin
  assume a b; rewrite left iff_equiv_eq';
  have h : π ((— a > — b) ⇔ (— — a < — — b)) { refine <_opp (— a) (— b) };
  apply ∧ᵢ
  { assume hab; refine ∧ₑ₂ h _; rewrite —_idem a; rewrite —_idem b; refine hab }
  { assume hn; rewrite left —_idem a; rewrite left —_idem b; refine ∧ₑ₁ h hn }
end;

opaque symbol ≤_opp_eq a b: π ((a ≤ b) = (— a ≥ — b)) ≔
begin
  assume a b; rewrite left iff_equiv_eq';
  have h : π ((— a ≥ — b) ⇔ (— — a ≤ — — b)) { refine ≤_opp (— a) (— b) };
  apply ∧ᵢ
  { assume hab; refine ∧ₑ₂ h _; rewrite —_idem a; rewrite —_idem b; refine hab }
  { assume hn; rewrite left —_idem a; rewrite left —_idem b; refine ∧ₑ₁ h hn }
end;

opaque symbol ≥_sub_eq a b: π ((a ≥ b) = (a - b ≥ 0)) ≔
begin
  assume a b; rewrite left iff_equiv_eq'; refine ∧ᵢ (≥_sub a b) (sub_≥ a b)
end;

opaque symbol >_sub_eq a b: π ((a > b) = (a - b > 0)) ≔
begin
  assume a b; rewrite left iff_equiv_eq'; refine ∧ᵢ (>_sub a b) (sub_> a b)
end;

opaque symbol >_0_eq_≥_1 d : π ((d > 0) = (d + — 1 ≥ 0)) ≔
begin
  induction
  { refine propExt _ _ (λ h, ⊥ₑ (h (λ x, x))) (λ h, ⊥ₑ (h ⊤ᵢ)) }
  { induction
    { assume q ih; refine propExt _ _ (λ _ h, h) (λ _ h, h ⊤ᵢ) }
    { assume q ih; refine propExt _ _ (λ _ h, h) (λ _ h, h ⊤ᵢ) }
    { refine propExt _ _ (λ _ h, h) (λ _ h, h ⊤ᵢ) } }
  { assume p; refine propExt _ _ (λ h, ⊥ₑ (h (λ x, x))) (λ h, ⊥ₑ (h ⊤ᵢ)) }
end;

opaque symbol >_eq_≥_succ a b: π ((a > b) = (a ≥ b + 1)) ≔
begin
  assume a b;
  rewrite >_sub_eq a b;
  rewrite ≥_sub_eq a (b + 1);
  have e : π (a - (b + 1) = (a - b) + — 1)
  { change π (a + — (b + 1) = (a + — b) + — 1);
    rewrite distr_—_+ b 1; rewrite left +_assoc a (— b) (— 1); reflexivity };
  rewrite e;
  refine >_0_eq_≥_1 (a - b)
end;

symbol =_sub_eq a b: π ((a = b) = (a - b = 0)) ≔
begin
  assume a b;
  rewrite left iff_equiv_eq';
  apply ∧ᵢ
  {
    assume h; rewrite h; simplify;
    apply -_same b;
  }
  {
      assume h;
      have g: π (((a - b) + b) = (0 + b)) { refine =_compat_add (a - b) 0 b h };
      have g2: π ((a + (— b + b)) = b) { rewrite left +_assoc; refine g };
      have g3: π ((a + 0) = b) { rewrite left -_same b; rewrite +_com b (— b); refine g2 };
      refine g3
    }
end;

opaque symbol ≠_compat_mul_l_eq (c a b: τ int) :
  π (istrue (not (isEq (c ≐ 0)))) → π ((¬ (a = b)) = ¬ (c * a = c * b)) ≔
begin
  assume c a b hc;
  have c≠0 : π (c ≠ 0)
  { assume h0; refine =⇒ (feq (λ x, istrue (not (isEq (x ≐ 0)))) h0) hc };
  apply feq (¬);
  rewrite left iff_equiv_eq';
  apply ∧ᵢ
  { assume heq; rewrite heq; reflexivity }
  { assume h; refine *_reg_r a b c c≠0 _; rewrite *_com a c; rewrite *_com b c; refine h }
end;

opaque symbol ¬_>_compat_mul_pos_l_eq c a b : π (0 < c) → π (¬ (a > b) = ¬ (c * a > c * b)) ≔
begin
  induction
  { assume a b hc; apply ⊥ₑ; refine hc }
  { assume p a b hc; apply feq (¬);
    rewrite *_com (Zpos p) a; rewrite *_com (Zpos p) b;
    rewrite left iff_equiv_eq'; refine >_compat_mul a b p }
  { assume p a b hc; apply ⊥ₑ; refine hc }
end;

opaque symbol ¬_≥_compat_mul_pos_l_eq c a b : π (0 < c) → π (¬ (a ≥ b) = ¬ (c * a ≥ c * b)) ≔
begin
  induction
  { assume a b hc; apply ⊥ₑ; refine hc }
  { assume p a b hc; apply feq (¬);
    rewrite *_com (Zpos p) a; rewrite *_com (Zpos p) b;
    rewrite left iff_equiv_eq'; refine ≥_compat_mul a b p }
  { assume p a b hc; apply ⊥ₑ; refine hc }
end;
opaque symbol la_mult_neg_eq [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 = t3) ⇒ (t1 * t2) = (t1 * t3)) ≔
begin
  assume t1 t2 t3 hc h; rewrite h; reflexivity
end;

opaque symbol la_mult_neg_lt t1 t2 t3 : π (t1 < 0) → π (t2 < t3) → π ((t1 * t2) > (t1 * t3)) ≔
begin
  induction
  { assume t2 t3 hc; apply ⊥ₑ; refine hc }
  { assume p t2 t3 hc; apply ⊥ₑ; refine hc }
  { assume p t2 t3 hc h;
    rewrite *_com (Zneg p) t2; rewrite *_com (Zneg p) t3;
    refine <_¬_≤ (t3 * Zneg p) (t2 * Zneg p) (∧ₑ₁ (<_compat_mul_neg (Zpos p) ⊤ᵢ t2 t3) h) }
end;

opaque symbol la_mult_neg_leq [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 ≤ t3) ⇒ (t1 * t2) ≥ (t1 * t3)) ≔
begin
  induction
  { assume t2 t3 hc; apply ⊥ₑ; refine hc }
  { assume p t2 t3 hc; apply ⊥ₑ; refine hc }
  { assume p t2 t3 hc h;
    rewrite *_com (Zneg p) t2; rewrite *_com (Zneg p) t3;
    refine ∧ₑ₂ (≥_≤ (t2 * Zneg p) (t3 * Zneg p)) (∧ₑ₁ (≤_compat_mul_neg (Zpos p) ⊤ᵢ t2 t3) h) }
end;

opaque symbol la_mult_neg_gt [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 > t3) ⇒ (t1 * t2) < (t1 * t3)) ≔
begin
  induction
  { assume t2 t3 hc; apply ⊥ₑ; refine hc }
  { assume p t2 t3 hc; apply ⊥ₑ; refine hc }
  { assume p t2 t3 hc h;
    rewrite *_com (Zneg p) t2; rewrite *_com (Zneg p) t3;
    refine ∧ₑ₁ (<_compat_mul_neg (Zpos p) ⊤ᵢ t3 t2) (∧ₑ₂ (<_> t3 t2) h) }
end;

opaque symbol la_mult_neg_ge [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 ≥ t3) ⇒ (t1 * t2) ≤ (t1 * t3)) ≔
begin
  induction
  { assume t2 t3 hc; apply ⊥ₑ; refine hc }
  { assume p t2 t3 hc; apply ⊥ₑ; refine hc }
  { assume p t2 t3 hc h;
    rewrite *_com (Zneg p) t2; rewrite *_com (Zneg p) t3;
    refine ∧ₑ₁ (≤_compat_mul_neg (Zpos p) ⊤ᵢ t3 t2) (∧ₑ₁ (≥_≤ t2 t3) h) }
end;

private symbol foo (X : τ int) :  π ((— _1 * (— _1 + X)) = (_1 + (— _1 * X))) ≔
begin
  assume X;
  rewrite left  .[x in x = _] reify_correct;
  rewrite left  .[x in _ = x] reify_correct;
  set l ≔ (reify ((— 1) * ((— 1) + (X))));
  set r ≔ (reify (1 + ((— 1) * (X))));
  rewrite .[x in val x = _] prodExt;
  rewrite .[x in _ = val x] prodExt;
  rewrite left  norm_correct ((l ₁)) ((l ₂));
  rewrite left  norm_correct ((r ₁)) ((r ₂));
  reflexivity
end;


/* ------------------------------------------------------------------------
   The Alethe la_* rules
   ------------------------------------------------------------------------ */

/* ------------------------------------------------------------------------
   poly_simp_rel over ℤ: `c₁·(x₁ − x₂) = c₂·(y₁ − y₂)` makes `x₁ ⋈ x₂` and
   `y₁ ⋈ y₂` the same proposition, for positive coefficients (any non-zero
   ones for `=`).
   ------------------------------------------------------------------------ */

// Scaling by a positive factor, as an equation between the inequalities
// themselves (the negated forms above are what la_generic needs).
opaque symbol ≥_mul_pos_eq c a b : π (0 < c) → π ((a ≥ b) = (c * a ≥ c * b)) ≔
begin
  assume c a b hc;
  rewrite left ¬¬ₑ_eq (a ≥ b); rewrite left ¬¬ₑ_eq (c * a ≥ c * b);
  rewrite ¬_≥_compat_mul_pos_l_eq c a b hc; reflexivity
end;

opaque symbol >_mul_pos_eq c a b : π (0 < c) → π ((a > b) = (c * a > c * b)) ≔
begin
  assume c a b hc;
  rewrite left ¬¬ₑ_eq (a > b); rewrite left ¬¬ₑ_eq (c * a > c * b);
  rewrite ¬_>_compat_mul_pos_l_eq c a b hc; reflexivity
end;

// `c ≠ 0` is taken as `istrue (not (isEq (c ≐ 0)))`, which computes to ⊤ for a
// numeral, like `≠_compat_mul_l_eq` above.
opaque symbol ≠0_of_≐ c : π (istrue (not (isEq (c ≐ 0)))) → π (c ≠ 0) ≔
begin
  assume c h; refine ≐_decides_neq _; assume hEq;
  have h' : π (istrue (not (isEq Eq))) { rewrite left hEq; refine h };
  refine h'
end;

opaque symbol Zpoly_rel_eq c1 x1 x2 c2 y1 y2 :
  π (istrue (not (isEq (c1 ≐ 0)))) → π (istrue (not (isEq (c2 ≐ 0)))) →
  π (c1 * (x1 - x2) = c2 * (y1 - y2)) → π ((x1 = x2) = (y1 = y2)) ≔
begin
  assume c1 x1 x2 c2 y1 y2 h1 h2 h;
  rewrite =_sub_eq x1 x2; rewrite =_sub_eq y1 y2;
  refine propExt _ _ _ _
  { assume e; refine *_reg_r (y1 - y2) 0 c2 (≠0_of_≐ c2 h2) _;
    rewrite *_com (y1 - y2) c2; rewrite left h; rewrite e; reflexivity }
  { assume e; refine *_reg_r (x1 - x2) 0 c1 (≠0_of_≐ c1 h1) _;
    rewrite *_com (x1 - x2) c1; rewrite h; rewrite e; reflexivity }
end;

opaque symbol Zpoly_rel_ge_pos c1 x1 x2 c2 y1 y2 : π (0 < c1) → π (0 < c2) →
  π (c1 * (x1 - x2) = c2 * (y1 - y2)) → π ((x1 ≥ x2) = (y1 ≥ y2)) ≔
begin
  assume c1 x1 x2 c2 y1 y2 h1 h2 h;
  rewrite ≥_sub_eq x1 x2; rewrite ≥_sub_eq y1 y2;
  rewrite ≥_mul_pos_eq c1 (x1 - x2) 0 h1; rewrite ≥_mul_pos_eq c2 (y1 - y2) 0 h2;
  rewrite h; reflexivity
end;

opaque symbol Zpoly_rel_gt_pos c1 x1 x2 c2 y1 y2 : π (0 < c1) → π (0 < c2) →
  π (c1 * (x1 - x2) = c2 * (y1 - y2)) → π ((x1 > x2) = (y1 > y2)) ≔
begin
  assume c1 x1 x2 c2 y1 y2 h1 h2 h;
  rewrite >_sub_eq x1 x2; rewrite >_sub_eq y1 y2;
  rewrite >_mul_pos_eq c1 (x1 - x2) 0 h1; rewrite >_mul_pos_eq c2 (y1 - y2) 0 h2;
  rewrite h; reflexivity
end;

opaque symbol Zpoly_rel_le_pos c1 x1 x2 c2 y1 y2 : π (0 < c1) → π (0 < c2) →
  π (c1 * (x1 - x2) = c2 * (y1 - y2)) → π ((x1 ≤ x2) = (y1 ≤ y2)) ≔
begin
  assume c1 x1 x2 c2 y1 y2 h1 h2 h;
  rewrite ≤_eq_¬_> x1 x2; rewrite ≤_eq_¬_> y1 y2; apply feq (¬);
  refine Zpoly_rel_gt_pos c1 x1 x2 c2 y1 y2 h1 h2 h
end;

opaque symbol Zpoly_rel_lt_pos c1 x1 x2 c2 y1 y2 : π (0 < c1) → π (0 < c2) →
  π (c1 * (x1 - x2) = c2 * (y1 - y2)) → π ((x1 < x2) = (y1 < y2)) ≔
begin
  assume c1 x1 x2 c2 y1 y2 h1 h2 h;
  rewrite <_eq_¬_≥ x1 x2; rewrite <_eq_¬_≥ y1 y2; apply feq (¬);
  refine Zpoly_rel_ge_pos c1 x1 x2 c2 y1 y2 h1 h2 h
end;

/* ------------------------------------------------------------------------
   la_generic by reflection.

   A step `(cl φ₁ … φₙ) :rule la_generic :args (a₁ … aₙ)` is proved by the one
   tactic `refine (Zla_generic (a₁ ⸬ … ⸬ □) (φ₁ ⸬ … ⸬ □) ⊤ᵢ)`. The clause is
   reified into the syntax below, `check` computes the Farkas combination of
   the negated literals scaled by the coefficients and decides whether its
   normal form is a contradictory constant, and `Zla_generic_sound` turns
   `check … = true` into the clause. The `:args` are the certificate; nothing
   is searched for.

   `≤`, `≥`, `>` and `¬` are definitions, and a rewrite rule cannot match a
   defined symbol (it is unfolded first), so the syntax is over the stuck
   shapes `istrue (isLt (a ≐ b))`, `istrue (isGt (a ≐ b))`, `a = b` and
   `p ⇒ ⊥`, and the denotation produces exactly those: the denotation of the
   reified clause is then convertible to the clause itself, which is all the
   final `refine` needs. No lemma `zdenote (rfyE x) = x` is ever stated.
   ------------------------------------------------------------------------ */

// The syntax of a linear integer term, over atoms numbered in an environment.
inductive ZExpr : TYPE ≔
| ZEAdd : ZExpr → ZExpr → ZExpr
| ZEOpp : ZExpr → ZExpr
| ZECst : ℤ → ZExpr
| ZEMul : ℤ → ZExpr → ZExpr    // k * e
| ZEMulr : ZExpr → ℤ → ZExpr   // e * k
| ZEAtom : ℕ → ZExpr
;

constant symbol zexpr : Set;
rule τ zexpr ↪ ZExpr;

symbol zdenote : ZExpr → 𝕃 int → ℤ;
rule zdenote (ZEAdd $a $b) $l ↪ zdenote $a $l + zdenote $b $l
with zdenote (ZEOpp $a) $l ↪ — (zdenote $a $l)
with zdenote (ZECst $k) _ ↪ $k
with zdenote (ZEMul $k $a) $l ↪ $k * zdenote $a $l
with zdenote (ZEMulr $a $k) $l ↪ zdenote $a $l * $k
with zdenote (ZEAtom $i) $l ↪ nth $l $i;

/* Reification of a ℤ term into its syntax and the list of its atoms, so that
   `zdenote` of the result is the term again by computation. Subtraction needs
   no rule: `x - y` unfolds to `x + — y`. WARNING: rfyE is sequential; the
   soundness lemmas below never reduce it on a variable. */
sequential symbol rfyE : 𝕃 int → ℤ → τ (zexpr × list int);

rule rfyE $l ($x + $y) ↪
  let x ≔ rfyE $l $x in let y ≔ rfyE (x ₂) $y in ZEAdd (x ₁) (y ₁) ‚ (y ₂)
with rfyE $l (— $x) ↪ let x ≔ rfyE $l $x in ZEOpp (x ₁) ‚ (x ₂)
with rfyE $l 0 ↪ ZECst 0 ‚ $l
with rfyE $l (Zpos $k) ↪ ZECst (Zpos $k) ‚ $l
with rfyE $l (Zneg $k) ↪ ZECst (Zneg $k) ‚ $l
with rfyE $l (Zpos $k * $x) ↪ let x ≔ rfyE $l $x in ZEMul (Zpos $k) (x ₁) ‚ (x ₂)
with rfyE $l (Zneg $k * $x) ↪ let x ≔ rfyE $l $x in ZEMul (Zneg $k) (x ₁) ‚ (x ₂)
with rfyE $l ($x * Zpos $k) ↪ let x ≔ rfyE $l $x in ZEMulr (x ₁) (Zpos $k) ‚ (x ₂)
with rfyE $l ($x * Zneg $k) ↪ let x ≔ rfyE $l $x in ZEMulr (x ₁) (Zneg $k) ‚ (x ₂)
// other terms are atoms, identified up to conversion
with rfyE $l $x ↪
  case (index _0 $x $l) (λ i, ZEAtom i ‚ $l) (λ i, ZEAtom i ‚ ($l ++ ($x ⸬ □)));

// The linear form of a syntax tree, in the monomial lists `norm_speed` sorts.
symbol zlin : ZExpr → 𝕃 grp;
rule zlin (ZEAdd $a $b) ↪ zlin $a ++ zlin $b
with zlin (ZEOpp $a) ↪ opp (zlin $a)
with zlin (ZECst $k) ↪ Cst $k ⸬ □
with zlin (ZEMul $k $a) ↪ mul $k (zlin $a)
with zlin (ZEMulr $a $k) ↪ mul $k (zlin $a)
with zlin (ZEAtom $i) ↪ Var $i 1 ⸬ □;

opaque symbol mul_correct l k g : π (val ((mul k g) ‚ l) = k * val (g ‚ l)) ≔
begin
  assume l k;
  induction
  { reflexivity }
  { induction
    { assume c xs ih;
      change π (k * c + val ((mul k xs) ‚ l) = k * (c + val (xs ‚ l)));
      rewrite ih; symmetry; refine *_distr_l k c (val (xs ‚ l)) }
    { assume i c xs ih;
      change π ((nth l i * (k * c)) + val ((mul k xs) ‚ l) = k * ((nth l i * c) + val (xs ‚ l)));
      rewrite ih; rewrite *_distr_l k (nth l i * c) (val (xs ‚ l));
      rewrite *_com k (nth l i * c); rewrite *_assoc (nth l i) c k; rewrite *_com c k;
      reflexivity } }
end;

opaque symbol neg_one_mul v : π (— 1 * v = — v) ≔
begin
  induction
  { reflexivity }
  { assume p; reflexivity }
  { assume p; reflexivity }
end;

opaque symbol opp_correct l g : π (val ((opp g) ‚ l) = — val (g ‚ l)) ≔
begin
  assume l g;
  change π (val ((mul (— 1) g) ‚ l) = — val (g ‚ l));
  rewrite mul_correct l (— 1) g; refine neg_one_mul (val (g ‚ l))
end;

opaque symbol zlin_correct l e : π (val ((zlin e) ‚ l) = zdenote e l) ≔
begin
  assume l;
  induction
  // ZEAdd
  { assume a ha b hb;
    change π (val ((zlin a ++ zlin b) ‚ l) = zdenote a l + zdenote b l);
    rewrite ++_eq_+ l (zlin a) (zlin b); rewrite ha; rewrite hb; reflexivity }
  // ZEOpp
  { assume a ha;
    change π (val ((opp (zlin a)) ‚ l) = — zdenote a l);
    rewrite opp_correct l (zlin a); rewrite ha; reflexivity }
  // ZECst
  { assume k; reflexivity }
  // ZEMul
  { assume k a ha;
    change π (val ((mul k (zlin a)) ‚ l) = k * zdenote a l);
    rewrite mul_correct l k (zlin a); rewrite ha; reflexivity }
  // ZEMulr
  { assume a ha k;
    change π (val ((mul k (zlin a)) ‚ l) = zdenote a l * k);
    rewrite mul_correct l k (zlin a); rewrite ha; refine *_com k (zdenote a l) }
  // ZEAtom
  { assume i; refine *_neutral (nth l i) }
end;

/* The literals of a clause. `BGt` is the raw `istrue (isGt (a ≐ b))`, i.e. the
   body of `a ≤ b`'s definition under its `¬`; `a > b` is two `LNeg`s on it. */
inductive BRel : TYPE ≔
| BEq : BRel
| BLt : BRel
| BGt : BRel
;

inductive ZLit : TYPE ≔
| LRel : BRel → ZExpr → ZExpr → ZLit
| LNeg : ZLit → ZLit
| LTop : ZLit   // a literal between numerals that computed to ⊤
| LBot : ZLit   // … or to ⊥
;

constant symbol zlit : Set;
rule τ zlit ↪ ZLit;

symbol denote_lit : ZLit → 𝕃 int → Prop;
rule denote_lit (LRel BLt $a $b) $l ↪ istrue (isLt (zdenote $a $l ≐ zdenote $b $l))
with denote_lit (LRel BGt $a $b) $l ↪ istrue (isGt (zdenote $a $l ≐ zdenote $b $l))
with denote_lit (LRel BEq $a $b) $l ↪ zdenote $a $l = zdenote $b $l
with denote_lit (LNeg $x) $l ↪ ¬ (denote_lit $x $l)
with denote_lit LTop _ ↪ ⊤
with denote_lit LBot _ ↪ ⊥;

// Sequential only to silence the critical pairs on numerals (`istrue (isLt
// (0 ≐ 0))` is also `⊥`): there is no catch-all, so no rule fires on a variable.
sequential symbol rfy_lit : 𝕃 int → Prop → τ (zlit × list int);
rule rfy_lit $l (istrue (isLt ($a ≐ $b))) ↪
  let a ≔ rfyE $l $a in let b ≔ rfyE (a ₂) $b in LRel BLt (a ₁) (b ₁) ‚ (b ₂)
with rfy_lit $l (istrue (isGt ($a ≐ $b))) ↪
  let a ≔ rfyE $l $a in let b ≔ rfyE (a ₂) $b in LRel BGt (a ₁) (b ₁) ‚ (b ₂)
with rfy_lit $l (@= int $a $b) ↪
  let a ≔ rfyE $l $a in let b ≔ rfyE (a ₂) $b in LRel BEq (a ₁) (b ₁) ‚ (b ₂)
with rfy_lit $l ($p ⇒ ⊥) ↪ let p ≔ rfy_lit $l $p in LNeg (p ₁) ‚ (p ₂)
with rfy_lit $l ⊤ ↪ LTop ‚ $l
with rfy_lit $l ⊥ ↪ LBot ‚ $l;

symbol denote_clause : 𝕃 zlit → 𝕃 int → Prop;
rule denote_clause □ _ ↪ ⊥
with denote_clause ($x ⸬ $xs) $l ↪ denote_lit $x $l ∨ denote_clause $xs $l;

symbol rfy_clause : 𝕃 int → 𝕃 o → τ (list zlit × list int);
rule rfy_clause $l □ ↪ □ ‚ $l
with rfy_clause $l ($x ⸬ $xs) ↪
  let x ≔ rfy_lit $l $x in let xs ≔ rfy_clause (x ₂) $xs in ((x ₁) ⸬ (xs ₁)) ‚ (xs ₂);

// The shapes the translator prints, and that they denote back to themselves.
private symbol x0 : τ int;
private symbol x1 : τ int;
assert ⊢ rfy_clause □ ((¬ (x0 ≤ x1)) ⸬ (x0 < x1) ⸬ (x1 ≥ Zpos H * x0) ⸬ (x0 = x1) ⸬ □) ≡
  (LNeg (LNeg (LRel BGt (ZEAtom _0) (ZEAtom (_0 +1))))
   ⸬ LRel BLt (ZEAtom _0) (ZEAtom (_0 +1))
   ⸬ LNeg (LRel BLt (ZEAtom (_0 +1)) (ZEMul (Zpos H) (ZEAtom _0)))
   ⸬ LRel BEq (ZEAtom _0) (ZEAtom (_0 +1))
   ⸬ □) ‚ (x0 ⸬ x1 ⸬ □);
assert ⊢ denote_clause (rfy_clause □ ((¬ (x0 ≤ x1)) ⸬ (x0 + — 1 + x1 > x1 - x0) ⸬ (Zneg H * x0 + 0 ≤ x1 * 2) ⸬ □) ₁)
                       (rfy_clause □ ((¬ (x0 ≤ x1)) ⸬ (x0 + — 1 + x1 > x1 - x0) ⸬ (Zneg H * x0 + 0 ≤ x1 * 2) ⸬ □) ₂)
  ≡ (¬ (x0 ≤ x1)) ∨ (x0 + — 1 + x1 > x1 - x0) ∨ (Zneg H * x0 + 0 ≤ x1 * 2) ∨ ⊥;
// comparisons of numerals compute away (`0 ≤ 1` is `⊥ ⇒ ⊥`); `=` never computes
assert ⊢ rfy_clause □ ((0 ≤ 1) ⸬ (¬ (0 = 0)) ⸬ □)
  ≡ (LNeg LBot ⸬ LNeg (LRel BEq (ZECst 0) (ZECst 0)) ⸬ □) ‚ □;

/* The certificate checker. The hypotheses are the negations of the clause's
   literals; `neg_s`/`neg_k` give the negation of a literal as `s ⋈ 0`, with
   `s : 𝕃 grp` and ⋈ ∈ {=, ≥} -- over ℤ a strict `s > 0` is `s - 1 ≥ 0`
   (Alethe's step 4) -- and `pos_s`/`pos_k` the literal itself, for the `LNeg`
   case. `combine` scales each hypothesis by its coefficient (|a| for an
   inequality, a for an equality, as the rule says) and sums; `contra` reads
   the sign of the normal form of the sum. */

inductive Cmp : TYPE ≔
| Ceq : Cmp
| Cge : Cmp
;

symbol join : Cmp → Cmp → Cmp;
rule join Ceq $k ↪ $k
with join Cge _ ↪ Cge;

symbol hyp_val : ℤ → Cmp → Prop;
rule hyp_val $v Cge ↪ $v ≥ 0
with hyp_val $v Ceq ↪ $v = 0;

symbol neg_s : ZLit → 𝕃 grp;
symbol pos_s : ZLit → 𝕃 grp;
rule neg_s (LRel BLt $a $b) ↪ zlin $a ++ opp (zlin $b)                     // ¬(a < b): a - b ≥ 0
with neg_s (LRel BGt $a $b) ↪ zlin $b ++ opp (zlin $a)                     // a ≤ b: b - a ≥ 0
with neg_s (LRel BEq _ _) ↪ □                                              // a ≠ b: unusable, 0 ≥ 0
with neg_s (LNeg $x) ↪ pos_s $x
with neg_s LTop ↪ Cst (— 1) ⸬ □                                            // ¬⊤: absurd, -1 ≥ 0
with neg_s LBot ↪ □
with pos_s (LRel BLt $a $b) ↪ zlin $b ++ opp (zlin $a) ++ (Cst (— 1) ⸬ □)  // a < b: b - a - 1 ≥ 0
with pos_s (LRel BGt $a $b) ↪ zlin $a ++ opp (zlin $b) ++ (Cst (— 1) ⸬ □)  // a > b: a - b - 1 ≥ 0
with pos_s (LRel BEq $a $b) ↪ zlin $a ++ opp (zlin $b)                     // a = b: a - b = 0
with pos_s (LNeg $x) ↪ neg_s $x
with pos_s LTop ↪ □
with pos_s LBot ↪ Cst (— 1) ⸬ □;

symbol neg_k : ZLit → Cmp;
symbol pos_k : ZLit → Cmp;
rule neg_k (LRel _ _ _) ↪ Cge
with neg_k (LNeg $x) ↪ pos_k $x
with neg_k LTop ↪ Cge
with neg_k LBot ↪ Cge
with pos_k (LRel BEq _ _) ↪ Ceq
with pos_k (LRel BLt _ _) ↪ Cge
with pos_k (LRel BGt _ _) ↪ Cge
with pos_k (LNeg $x) ↪ neg_k $x
with pos_k LTop ↪ Cge
with pos_k LBot ↪ Cge;

symbol zabs : ℤ → ℤ;
rule zabs Z0 ↪ Z0
with zabs (Zpos $p) ↪ Zpos $p
with zabs (Zneg $p) ↪ Zpos $p;

symbol coef : ℤ → Cmp → ℤ;
rule coef $c Ceq ↪ $c
with coef $c Cge ↪ zabs $c;

// A literal without a coefficient is dropped, which only weakens the sum.
symbol combine_s : 𝕃 int → 𝕃 zlit → 𝕃 grp;
rule combine_s _ □ ↪ □
with combine_s □ (_ ⸬ _) ↪ □
with combine_s ($c ⸬ $cs) ($x ⸬ $xs) ↪ mul (coef $c (neg_k $x)) (neg_s $x) ++ combine_s $cs $xs;

symbol combine_k : 𝕃 int → 𝕃 zlit → Cmp;
rule combine_k _ □ ↪ Ceq
with combine_k □ (_ ⸬ _) ↪ Ceq
with combine_k ($c ⸬ $cs) ($x ⸬ $xs) ↪ join (neg_k $x) (combine_k $cs $xs);

// On a normal form: a lone negative constant contradicts `≥ 0` and `= 0`, a
// lone positive one only `= 0`. No catch-all.
symbol contra : 𝕃 grp → Cmp → 𝔹;
rule contra □ _ ↪ false
with contra (_ ⸬ (_ ⸬ _)) _ ↪ false
with contra (Var _ _ ⸬ □) _ ↪ false
with contra (Cst Z0 ⸬ □) _ ↪ false
with contra (Cst (Zneg _) ⸬ □) _ ↪ true
with contra (Cst (Zpos _) ⸬ □) Cge ↪ false
with contra (Cst (Zpos _) ⸬ □) Ceq ↪ true;

symbol check (cs : 𝕃 int) (ls : 𝕃 zlit) : 𝔹 ≔
  contra (norm_speed (combine_s cs ls)) (combine_k cs ls);

// `(cl (not (<= a b)) (<= a b))` with coefficients 1 1, and a wrong certificate
assert ⊢ check (Zpos H ⸬ Zpos H ⸬ □) (rfy_clause □ ((¬ (x0 ≤ x1)) ⸬ (x0 ≤ x1) ⸬ □) ₁) ≡ true;
assertnot ⊢ check (Zpos H ⸬ Zpos H ⸬ □) (rfy_clause □ ((¬ (x0 ≤ x1)) ⸬ (x0 ≤ x0) ⸬ □) ₁) ≡ true;
// `(cl (not (<= (- 1) n)) (not (<= (- 1) (+ n m))) (<= (- 2) (* 2 n)) (not (<= m 1)))`, needs
// the gcd strengthening of Carcara's checker: not supported, the checker must say no
assertnot ⊢ check (Zpos H ⸬ Zpos H ⸬ Zpos H ⸬ Zpos H ⸬ □)
  (rfy_clause □ ((¬ (Zneg H ≤ x0)) ⸬ (¬ (Zneg H ≤ x0 + x1)) ⸬ (Zneg (O H) ≤ Zpos (O H) * x0) ⸬ (¬ (x1 ≤ Zpos H)) ⸬ □) ₁) ≡ true;

/* Soundness. One hypothesis first: each relation, as the definitions of
   ≤ ≥ > unfold, in the `s ⋈ 0` form of `neg_s`/`pos_s`. */

opaque symbol ge_sound a b : π (¬ (a < b)) → π (a + — b ≥ 0) ≔
begin
  assume a b h; refine ≥_sub a b h
end;

opaque symbol le_sound a b : π (¬ (istrue (isGt (a ≐ b)))) → π (b + — a ≥ 0) ≔
begin
  assume a b h; refine ≥_sub b a (∧ₑ₂ (≥_≤ b a) h)
end;

opaque symbol lt_sound a b : π (a < b) → π (b + (— a + — 1) ≥ 0) ≔
begin
  assume a b h;
  have g : π (b - a > 0) { refine >_sub b a (∧ₑ₁ (<_> a b) h) };
  have g1 : π ((b - a) + — 1 ≥ 0) { rewrite left >_0_eq_≥_1 (b - a); refine g };
  rewrite left +_assoc b (— a) (— 1); refine g1
end;

opaque symbol gt_sound a b : π (istrue (isGt (a ≐ b))) → π (a + (— b + — 1) ≥ 0) ≔
begin
  assume a b h;
  have g : π (a - b > 0) { refine >_sub a b (λ k, k h) };
  have g1 : π ((a - b) + — 1 ≥ 0) { rewrite left >_0_eq_≥_1 (a - b); refine g };
  rewrite left +_assoc a (— b) (— 1); refine g1
end;

opaque symbol eq_sound a b : π (a = b) → π (a + — b = 0) ≔
begin
  assume a b h; rewrite h; refine -_same b
end;

// The negation of a literal gives its `neg_s`, the literal its `pos_s`; both
// together, so that `LNeg` flips them.
opaque symbol lit_sound l : Π x,
  π ((¬ (denote_lit x l) ⇒ hyp_val (val ((neg_s x) ‚ l)) (neg_k x))
     ∧ (denote_lit x l ⇒ hyp_val (val ((pos_s x) ‚ l)) (pos_k x))) ≔
begin
  assume l;
  induction
  // LRel r a b
  { induction
    // BEq
    { assume a b; refine ∧ᵢ _ _
      { assume h; refine ≥_refl 0 }
      { assume h;
        change π (val ((zlin a ++ opp (zlin b)) ‚ l) = 0);
        rewrite ++_eq_+ l (zlin a) (opp (zlin b)); rewrite opp_correct l (zlin b);
        rewrite zlin_correct l a; rewrite zlin_correct l b;
        refine eq_sound (zdenote a l) (zdenote b l) h } }
    // BLt
    { assume a b; refine ∧ᵢ _ _
      { assume h;
        change π (val ((zlin a ++ opp (zlin b)) ‚ l) ≥ 0);
        rewrite ++_eq_+ l (zlin a) (opp (zlin b)); rewrite opp_correct l (zlin b);
        rewrite zlin_correct l a; rewrite zlin_correct l b;
        refine ge_sound (zdenote a l) (zdenote b l) h }
      { assume h;
        change π (val ((zlin b ++ opp (zlin a) ++ (Cst (— 1) ⸬ □)) ‚ l) ≥ 0);
        rewrite ++_eq_+ l (zlin b) (opp (zlin a) ++ (Cst (— 1) ⸬ □));
        rewrite ++_eq_+ l (opp (zlin a)) (Cst (— 1) ⸬ □);
        rewrite opp_correct l (zlin a); rewrite zlin_correct l a; rewrite zlin_correct l b;
        refine lt_sound (zdenote a l) (zdenote b l) h } }
    // BGt
    { assume a b; refine ∧ᵢ _ _
      { assume h;
        change π (val ((zlin b ++ opp (zlin a)) ‚ l) ≥ 0);
        rewrite ++_eq_+ l (zlin b) (opp (zlin a)); rewrite opp_correct l (zlin a);
        rewrite zlin_correct l a; rewrite zlin_correct l b;
        refine le_sound (zdenote a l) (zdenote b l) h }
      { assume h;
        change π (val ((zlin a ++ opp (zlin b) ++ (Cst (— 1) ⸬ □)) ‚ l) ≥ 0);
        rewrite ++_eq_+ l (zlin a) (opp (zlin b) ++ (Cst (— 1) ⸬ □));
        rewrite ++_eq_+ l (opp (zlin b)) (Cst (— 1) ⸬ □);
        rewrite opp_correct l (zlin b); rewrite zlin_correct l a; rewrite zlin_correct l b;
        refine gt_sound (zdenote a l) (zdenote b l) h } } }
  // LNeg x
  { assume x ih; refine ∧ᵢ _ _
    { assume h; refine ∧ₑ₂ ih (¬¬ₑ (denote_lit x l) h) }
    { assume h; refine ∧ₑ₁ ih h } }
  // LTop
  { refine ∧ᵢ _ _
    { assume h; refine ⊥ₑ (h ⊤ᵢ) }
    { assume h; refine ≥_refl 0 } }
  // LBot
  { refine ∧ᵢ _ _
    { assume h; refine ≥_refl 0 }
    { assume h; refine ⊥ₑ h } }
end;

opaque symbol hyp_ge v : Π k, π (hyp_val v k) → π (v ≥ 0) ≔
begin
  assume v; induction
  { assume h; refine =_≥ v 0 h }
  { assume h; refine h }
end;

// Scaling by the coefficient: |c| ≥ 0 keeps `≥ 0`, any c keeps `= 0`.
opaque symbol scale_sound v k : π (hyp_val v k) → Π c, π (hyp_val (coef c k * v) k) ≔
begin
  assume v; induction
  // Ceq
  { assume h c; change π (c * v = 0); rewrite h; reflexivity }
  // Cge
  { assume h; induction
    { refine ≥_refl 0 }
    { assume p; refine ≥_compat_mul_pos_l (Zpos p) v 0 (λ x, x ⊤ᵢ) h }
    { assume p; refine ≥_compat_mul_pos_l (Zpos p) v 0 (λ x, x ⊤ᵢ) h } }
end;

opaque symbol add_sound_eq v1 v2 : π (v1 = 0) → Π k2, π (hyp_val v2 k2) → π (hyp_val (v1 + v2) k2) ≔
begin
  assume v1 v2 h1; induction
  { assume h2; change π (v1 + v2 = 0); rewrite h1; rewrite h2; reflexivity }
  { assume h2; change π (v1 + v2 ≥ 0); refine ≥_add_≥ v1 0 v2 0 (=_≥ v1 0 h1) h2 }
end;

opaque symbol add_sound v1 v2 k2 :
  π (hyp_val v2 k2) → Π k1, π (hyp_val v1 k1) → π (hyp_val (v1 + v2) (join k1 k2)) ≔
begin
  assume v1 v2 k2 h2; induction
  { assume h1; refine add_sound_eq v1 v2 h1 k2 h2 }
  { assume h1; change π (v1 + v2 ≥ 0); refine ≥_add_≥ v1 0 v2 0 h1 (hyp_ge v2 k2 h2) }
end;

// The sign of a normal form decides, by computation on the numeral.
opaque symbol contra_sound_ge l g : π (istrue (contra g Cge)) → π (val (g ‚ l) ≥ 0) → π ⊥ ≔
begin
  assume l g;
  refine case_𝕃2 (λ g, istrue (contra g Cge) ⇒ val (g ‚ l) ≥ 0 ⇒ ⊥) _ _ _ g
  { assume h; refine ⊥ₑ h }
  { induction
    { induction
      { assume h; refine ⊥ₑ h }
      { assume p h; refine ⊥ₑ h }
      { assume p h hv; refine hv ⊤ᵢ } }
    { assume i z h; refine ⊥ₑ h } }
  { assume x y g' h; refine ⊥ₑ h }
end;

opaque symbol contra_sound_eq l g : π (istrue (contra g Ceq)) → π (val (g ‚ l) = 0) → π ⊥ ≔
begin
  assume l g;
  refine case_𝕃2 (λ g, istrue (contra g Ceq) ⇒ val (g ‚ l) = 0 ⇒ ⊥) _ _ _ g
  { assume h; refine ⊥ₑ h }
  { induction
    { induction
      { assume h; refine ⊥ₑ h }
      { assume p h e; refine Zpos≠Z0 p e }
      { assume p h e; refine Zneg≠Z0 p e } }
    { assume i z h; refine ⊥ₑ h } }
  { assume x y g' h; refine ⊥ₑ h }
end;

opaque symbol contra_sound l g : Π k, π (istrue (contra g k)) → π (hyp_val (val (g ‚ l)) k) → π ⊥ ≔
begin
  assume l g; induction
  { refine contra_sound_eq l g }
  { refine contra_sound_ge l g }
end;

opaque symbol check_sound l cs ls :
  π (istrue (check cs ls)) → π (hyp_val (val ((combine_s cs ls) ‚ l)) (combine_k cs ls)) → π ⊥ ≔
begin
  assume l cs ls h hv;
  refine contra_sound l (norm_speed (combine_s cs ls)) (combine_k cs ls) h _;
  rewrite norm_correct (combine_s cs ls) l; refine hv
end;

/* The clause, by induction on its literals: each one is either true, which
   proves the clause, or false, which is one more hypothesis for the sum. The
   continuation stands for the hypotheses already collected. */
opaque symbol combine_sound l : Π ls cs,
  (π (hyp_val (val ((combine_s cs ls) ‚ l)) (combine_k cs ls)) → π ⊥) → π (denote_clause ls l) ≔
begin
  assume l;
  induction
  // □ : the sum is empty, `0 = 0`
  { assume cs H; refine H (eq_refl 0) }
  // x ⸬ xs
  { assume x xs ih; induction
    // no coefficient left
    { assume H; refine ⊥ₑ (H (eq_refl 0)) }
    { assume c cs ihc H;
      refine ∨ₑ (em (denote_lit x l)) (λ d, ∨ᵢ₁ d) _;
      assume nd; refine ∨ᵢ₂ _; refine ih cs _; assume hh; refine H _;
      change π (hyp_val (val ((mul (coef c (neg_k x)) (neg_s x) ++ combine_s cs xs) ‚ l))
                        (join (neg_k x) (combine_k cs xs)));
      rewrite ++_eq_+ l (mul (coef c (neg_k x)) (neg_s x)) (combine_s cs xs);
      rewrite mul_correct l (coef c (neg_k x)) (neg_s x);
      refine add_sound (coef c (neg_k x) * val ((neg_s x) ‚ l)) (val ((combine_s cs xs) ‚ l))
                       (combine_k cs xs) hh (neg_k x)
                       (scale_sound (val ((neg_s x) ‚ l)) (neg_k x) (∧ₑ₁ (lit_sound l x) nd) c) } }
end;

opaque symbol Zla_generic_sound cs ls l : π (istrue (check cs ls)) → π (denote_clause ls l) ≔
begin
  assume cs ls l h; refine combine_sound l ls cs (check_sound l cs ls h)
end;

/* The tactic. `G` is the clause as the translator prints it, `cs` the step's
   coefficients; the type of `Zla_generic cs G ⊤ᵢ` is convertible to `π̇ G`, so
   `refine (Zla_generic cs G ⊤ᵢ)` closes the step. Opaque: only its type is
   ever used. */
opaque symbol Zla_generic (cs : 𝕃 int) (G : 𝕃 o) :
  π (istrue (check cs (rfy_clause □ G ₁))) → π (denote_clause (rfy_clause □ G ₁) (rfy_clause □ G ₂)) ≔
begin
  assume cs G h; refine Zla_generic_sound cs (rfy_clause □ G ₁) (rfy_clause □ G ₂) h
end;

require open alethe.core;

opaque symbol la_disequality (t1 t2: τ int) : π̇ (((t1 = t2) ∨ ¬ (t1 ≤ t2) ∨ ¬ (t2 ≤ t1)) ⸬ □) ≔
begin
  assume t1 t2;
  apply ∨ᵢ₁;
  rewrite ∨_com;
  rewrite ∨_assoc;
  rewrite imp_eq_or;
  rewrite imp_eq_or;
  refine ≤_antisym t1 t2
end;

opaque symbol la_totality (t1 t2: τ int) : π̇ (((t1 ≤ t2) ∨ (t2 ≤ t1)) ⸬ □) ≔
begin
  assume x y;
  apply ∨ᵢ₁;
  have e : π (¬ (istrue(isGt (x ≐ y))) ∨ ¬ (istrue(isGt (y ≐ x))))
  { rewrite ≐_com;
    refine ind_Comp (λ c, ((y ≐ x) = c) ⇒ ¬ (istrue(isGt (Stdlib.Comp.opp c))) ∨ ¬ (istrue(isGt c))) _ _ _ (y ≐ x) _
    { assume H; simplify; apply ∨ᵢ₁; refine (λ x, x) }
    { assume H; simplify; apply ∨ᵢ₂; refine (λ x, x) }
    { assume H; simplify; apply ∨ᵢ₁; refine (λ x, x) }
    { rewrite ≐_com; reflexivity } };
  refine e
end;

/* ------------------------------------------------------------------------
   evaluate over ℤ: a comparison of numerals is ⊤ or ⊥, decided by `≐`
   (the equality case computes and closes by reflexivity).
   ------------------------------------------------------------------------ */

opaque symbol isEq_Eq c : π (istrue (isEq c)) → π (c = Eq) ≔
begin
  induction
  { assume h; reflexivity }
  { assume h; refine ⊥ₑ h }
  { assume h; refine ⊥ₑ h }
end;

opaque symbol Zeq_true a b : π (istrue (isEq (a ≐ b))) → π ((a = b) = ⊤) ≔
begin
  assume a b h; refine eq_⊤_intro (a = b) (≐_decides a b (isEq_Eq (a ≐ b) h))
end;

opaque symbol Zeq_false a b : π (istrue (not (isEq (a ≐ b)))) → π ((a = b) = ⊥) ≔
begin
  assume a b h;
  have hne : π (a ≐ b ≠ Eq)
  { assume hEq;
    have h' : π (istrue (not (isEq Eq))) { rewrite left hEq; refine h };
    refine h' };
  refine eq_⊥_intro (a = b) (≐_decides_neq hne)
end;

opaque symbol Zlt_true a b : π (istrue (isLt (a ≐ b))) → π ((a < b) = ⊤) ≔
begin
  assume a b h; refine eq_⊤_intro (a < b) h
end;

opaque symbol Zlt_false a b : π (istrue (not (isLt (a ≐ b)))) → π ((a < b) = ⊥) ≔
begin
  assume a b h; refine eq_⊥_intro (a < b) (istrue_not h)
end;

opaque symbol Zle_true a b : π (istrue (not (isGt (a ≐ b)))) → π ((a ≤ b) = ⊤) ≔
begin
  assume a b h; refine eq_⊤_intro (a ≤ b) (istrue_not h)
end;

opaque symbol Zle_false a b : π (istrue (isGt (a ≐ b))) → π ((a ≤ b) = ⊥) ≔
begin
  assume a b h; refine eq_⊥_intro (a ≤ b) (λ hle, hle h)
end;

opaque symbol Zge_true a b : π (istrue (not (isLt (a ≐ b)))) → π ((a ≥ b) = ⊤) ≔
begin
  assume a b h; refine eq_⊤_intro (a ≥ b) (istrue_not h)
end;

opaque symbol Zge_false a b : π (istrue (isLt (a ≐ b))) → π ((a ≥ b) = ⊥) ≔
begin
  assume a b h; refine eq_⊥_intro (a ≥ b) (λ hge, hge h)
end;

opaque symbol Zgt_true a b : π (istrue (isGt (a ≐ b))) → π ((a > b) = ⊤) ≔
begin
  assume a b h; refine eq_⊤_intro (a > b) (λ hle, hle h)
end;

opaque symbol Zgt_false a b : π (istrue (not (isGt (a ≐ b)))) → π ((a > b) = ⊥) ≔
begin
  assume a b h; refine eq_⊥_intro (a > b) (λ hgt, hgt (istrue_not h))
end;

// la_generic as one tactic: `(cl (not (<= n m)) (<= n m)) :args (1 1)`
private symbol la_generic_smoke (n m : τ int) : π̇ ((¬ (n ≤ m)) ⸬ (n ≤ m) ⸬ □) ≔
begin
  assume n m;
  refine Zla_generic (Stdlib.Z.1 ⸬ Stdlib.Z.1 ⸬ □) ((¬ (n ≤ m)) ⸬ (n ≤ m) ⸬ □) ⊤ᵢ
end;
