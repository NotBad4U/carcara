require Stdlib.Nat as Nat;
require open Stdlib.ExtraRules Stdlib.Z Stdlib.List Stdlib.PropExt;

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

opaque symbol eta_prod [a b] (x:τ(a × b)): π(x = (x ₁) ‚ (x ₂)) ≔
begin
  assume a b; induction; assume x y; reflexivity
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
  rewrite .[x in val x = _] eta_prod;
  rewrite .[x in _ = val x] eta_prod;
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
