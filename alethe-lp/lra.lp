require open Stdlib.List Stdlib.PropExt Stdlib.ExtraRules;
require open alethe.real;

inductive G: TYPE ≔
| Cst: ℚ → G
| Var: ℕ → ℚ → G
;

opaque symbol rec_G : Π p0: (G → Prop), (Π x0: ℚ, π (p0 (Cst x0))) → (Π x0: ℕ, Π x2: ℚ, π (p0 (Var x0 x2))) → Π x: G, π (p0 x) ≔ ind_G;

constant symbol grp : Set;
rule τ grp ↪ G;

// multiplication by a constant

symbol mul: ℚ → 𝕃 grp → 𝕃 grp;

rule mul $k ((Cst $l) ⸬ $xs) ↪ Cst ($k *𝕢 $l) ⸬ (mul $k $xs)
with mul $k ((Var $i $l) ⸬ $xs) ↪ Var $i ($k *𝕢 $l) ⸬ (mul $k $xs)
with mul _ □ ↪ □;

// opposite

symbol opp ≔ mul (—𝕢 1⫽1);


/* evaluation of an arithmetic expression wrt a list of values for variables
variables with indexes not in the list are interpreted by 0 */

symbol nth ≔ nth zero;

symbol val_grp: τ grp → 𝕃 real → τ real;
rule val_grp (Cst $k) _ ↪ lit $k
with val_grp (Var $i $k) $l ↪ ((nth $l $i) *ᵣ lit $k)
;

symbol val: τ(list grp × list real) → τ real;

rule val (□ ‚ _) ↪ zero
with val (($x ⸬ $xs) ‚ $l) ↪ (val_grp $x $l) ＋ᵣ (val ($xs ‚ $l));

symbol va l x ≔ val (x ‚ l);

// some useful type (use inductive instead?)

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
with index $k $x ($y ⸬ $l) ↪ index ($k Stdlib.Nat.+ Stdlib.Nat._1) $x $l;

// The syntax of a linear real term, over atoms numbered in an environment.

inductive Expr: TYPE ≔
| EAdd: Expr → Expr → Expr
| EOpp: Expr → Expr
| ECst: ℚ → Expr
| EMul: ℚ → Expr → Expr    // lit k *ᵣ e
| EMulr: Expr → ℚ → Expr   // e *ᵣ lit k
| EAtom: ℕ → Expr
;

constant symbol expr : Set;
rule τ expr ↪ Expr;

symbol denote: Expr → 𝕃 real → τ real;
rule denote (EAdd $a $b) $l ↪ denote $a $l ＋ᵣ denote $b $l
with denote (EOpp $a) $l ↪ —ᵣ (denote $a $l)
with denote (ECst $k) _ ↪ lit $k
with denote (EMul $k $a) $l ↪ lit $k *ᵣ denote $a $l
with denote (EMulr $a $k) $l ↪ denote $a $l *ᵣ lit $k
with denote (EAtom $i) $l ↪ nth $l $i;

/* reification: given a Lambdapi term x of type τ real, compute its syntax e
and the list l of its atoms, so that denote e l is x again by computation.
Subtraction needs no rule: x −ᵣ y unfolds to x ＋ᵣ —ᵣ y. WARNING: rfy is
sequential. */

sequential symbol rfy: τ(list real) → τ real → τ(expr × list real);

// addition
rule rfy $l ($x ＋ᵣ $y) ↪
  let x ≔ rfy $l $x in let y ≔ rfy (x ₂) $y in EAdd (x ₁) (y ₁) ‚ (y ₂)

// opposite
with rfy $l (—ᵣ $x) ↪ let x ≔ rfy $l $x in EOpp (x ₁) ‚ (x ₂)

// constants
with rfy $l (lit $k) ↪ ECst $k ‚ $l

// multiplication by a constant
with rfy $l ((lit $k) *ᵣ $x) ↪ let x ≔ rfy $l $x in EMul $k (x ₁) ‚ (x ₂)
with rfy $l ($x *ᵣ (lit $k)) ↪ let x ≔ rfy $l $x in EMulr (x ₁) $k ‚ (x ₂)

//other cases are abstracted by a variable
with rfy $l $x ↪
  case (index _0 $x $l) (λ i, EAtom i ‚ $l) (λ i, EAtom i ‚ ($l ++ ($x ⸬ □)))
;

symbol reify ≔ rfy □;

symbol lin: Expr → 𝕃 grp;
rule lin (EAdd $a $b) ↪ lin $a ++ lin $b
with lin (EOpp $a) ↪ opp (lin $a)
with lin (ECst $k) ↪ Cst $k ⸬ □
with lin (EMul $k $a) ↪ mul $k (lin $a)
with lin (EMulr $a $k) ↪ mul $k (lin $a)
with lin (EAtom $i) ↪ Var $i 1⫽1 ⸬ □;

symbol compN : ℕ → ℕ → Comp;

rule compN _0 _0 ↪ Eq
with compN _0 (_ +1) ↪ Lt
with compN (_ +1) _0 ↪ Gt
with compN ($x +1) ($y +1) ↪ compN $x $y;

symbol leG : τ grp → τ grp → 𝔹;
rule leG (Cst _) _ ↪ true
with leG (Var _ _) (Cst _) ↪ false
with leG (Var $i _) (Var $j _) ↪ $i Stdlib.Nat.≤ $j;

opaque symbol ++_eq_+ l x y : π (val ((x ++ y) ‚ l) = val (x ‚ l) ＋ᵣ val (y ‚ l)) ≔
begin
assume l;
induction
{ assume y; symmetry; refine add_zero_l (val (y ‚ l)) }
{
  assume x xs ih y;
  change π (val_grp x l ＋ᵣ val ((xs ++ y) ‚ l) = (val_grp x l ＋ᵣ val (xs ‚ l)) ＋ᵣ val (y ‚ l));
  rewrite ih y;
  symmetry; refine add_assoc (val_grp x l) (val (xs ‚ l)) (val (y ‚ l))
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

opaque symbol split_correct l g : π (val ((split g ₁) ‚ l) ＋ᵣ val ((split g ₂) ‚ l) = val (g ‚ l)) ≔
begin
  assume l;
  refine ind_𝕃2 (λ g, val ((split g ₁) ‚ l) ＋ᵣ val ((split g ₂) ‚ l) = val (g ‚ l)) _ _ _
  { refine add_zero_l zero }
  { assume x; refine add_zero_r (val ((x ⸬ □) ‚ l)) }
  { assume x y g ih;
    change π ((val_grp x l ＋ᵣ val ((split g ₁) ‚ l)) ＋ᵣ (val_grp y l ＋ᵣ val ((split g ₂) ‚ l))
              = val_grp x l ＋ᵣ (val_grp y l ＋ᵣ val (g ‚ l)));
    rewrite left ih;
    rewrite add_assoc (val_grp x l) (val ((split g ₁) ‚ l)) (val_grp y l ＋ᵣ val ((split g ₂) ‚ l));
    rewrite add_left_comm (val ((split g ₁) ‚ l)) (val_grp y l) (val ((split g ₂) ‚ l));
    reflexivity }
end;

opaque symbol merge_correct l (le : τ grp → τ grp → 𝔹) g1 g2 :
  π (val ((merge le g1 g2) ‚ l) = val (g1 ‚ l) ＋ᵣ val (g2 ‚ l)) ≔
begin
  assume l le;
  induction
  { assume g2; symmetry; refine add_zero_l (val (g2 ‚ l)) }
  { assume x xs ih;
    induction
    { symmetry; refine add_zero_r (val ((x ⸬ xs) ‚ l)) }
    { assume y ys ih2;
      // whichever monomial comes first
      refine ind_𝔹 (λ b, val ((if b (x ⸬ merge le xs (y ⸬ ys)) (y ⸬ merge le (x ⸬ xs) ys)) ‚ l)
                         = val ((x ⸬ xs) ‚ l) ＋ᵣ val ((y ⸬ ys) ‚ l)) _ _ (le x y)
      { change π (val_grp x l ＋ᵣ val ((merge le xs (y ⸬ ys)) ‚ l)
                  = (val_grp x l ＋ᵣ val (xs ‚ l)) ＋ᵣ val ((y ⸬ ys) ‚ l));
        rewrite ih (y ⸬ ys);
        symmetry; refine add_assoc (val_grp x l) (val (xs ‚ l)) (val ((y ⸬ ys) ‚ l)) }
      { change π (val_grp y l ＋ᵣ val ((merge le (x ⸬ xs) ys) ‚ l)
                  = val ((x ⸬ xs) ‚ l) ＋ᵣ (val_grp y l ＋ᵣ val (ys ‚ l)));
        rewrite ih2;
        refine add_left_comm (val_grp y l) (val ((x ⸬ xs) ‚ l)) (val (ys ‚ l)) } } }
end;

opaque symbol mergesort_correct l (le : τ grp → τ grp → 𝔹) g :
  π (val ((mergesort le g) ‚ l) = val (g ‚ l)) ≔
begin
  assume l le;
  refine ind_𝕃_size (λ g, val ((mergesort le g) ‚ l) = val (g ‚ l)) _;
  refine case_𝕃2
    (λ g, (`∀ g' : τ (list grp), istrue (size g' Stdlib.Nat.< size g)
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
with collect_from (Cst $c1) (Cst $c2 ⸬ $l) ↪ collect_from (Cst ($c1 𝕢+ $c2)) $l
with collect_from (Cst $c) (Var $j $k ⸬ $l) ↪ Cst $c ⸬ collect_from (Var $j $k) $l
with collect_from (Var $i $k) (Cst $c ⸬ $l) ↪ Var $i $k ⸬ collect_from (Cst $c) $l
with collect_from (Var $i $k1) (Var $j $k2 ⸬ $l) ↪
    case_Comp (compN $i $j)
        (collect_from (Var $i ($k1 𝕢+ $k2)) $l)
        (Var $i $k1 ⸬ collect_from (Var $j $k2) $l)
        (Var $i $k1 ⸬ collect_from (Var $j $k2) $l);

symbol collect : 𝕃 grp → 𝕃 grp;
rule collect □ ↪ □
with collect ($x ⸬ $l) ↪ collect_from $x $l;

opaque symbol collect_from_correct l g x : π (val ((collect_from x g) ‚ l) = val_grp x l ＋ᵣ val (g ‚ l)) ≔
begin
  assume l;
  induction
  { assume x; reflexivity }
  { induction
    // the next monomial is a constant
    { assume c2 g ih;
      induction
      { assume c1;
        change π (val ((collect_from (Cst (c1 𝕢+ c2)) g) ‚ l) = lit c1 ＋ᵣ (lit c2 ＋ᵣ val (g ‚ l)));
        rewrite ih (Cst (c1 𝕢+ c2));
        change π (lit (c1 𝕢+ c2) ＋ᵣ val (g ‚ l) = lit c1 ＋ᵣ (lit c2 ＋ᵣ val (g ‚ l)));
        rewrite lit_add c1 c2; refine add_assoc (lit c1) (lit c2) (val (g ‚ l)) }
      { assume i k;
        change π (val_grp (Var i k) l ＋ᵣ val ((collect_from (Cst c2) g) ‚ l)
                  = val_grp (Var i k) l ＋ᵣ val (((Cst c2) ⸬ g) ‚ l));
        rewrite ih (Cst c2); reflexivity } }
    // the next monomial is a variable
    { assume j k2 g ih;
      induction
      { assume c;
        change π (lit c ＋ᵣ val ((collect_from (Var j k2) g) ‚ l) = lit c ＋ᵣ val (((Var j k2) ⸬ g) ‚ l));
        rewrite ih (Var j k2); reflexivity }
      { assume i k1;
        refine ind_Comp (λ u, compN i j = u ⇒ val ((case_Comp u (collect_from (Var i (k1 𝕢+ k2)) g) (Var i k1 ⸬ collect_from (Var j k2) g) (Var i k1 ⸬ collect_from (Var j k2) g)) ‚ l) = val_grp (Var i k1) l ＋ᵣ val (((Var j k2) ⸬ g) ‚ l)) _ _ _ (compN i j) _
        // same variable
        { assume heq; rewrite compN_correct i j heq;
          change π (val ((collect_from (Var j (k1 𝕢+ k2)) g) ‚ l)
                    = (nth l j *ᵣ lit k1) ＋ᵣ ((nth l j *ᵣ lit k2) ＋ᵣ val (g ‚ l)));
          rewrite ih (Var j (k1 𝕢+ k2));
          change π ((nth l j *ᵣ lit (k1 𝕢+ k2)) ＋ᵣ val (g ‚ l)
                    = (nth l j *ᵣ lit k1) ＋ᵣ ((nth l j *ᵣ lit k2) ＋ᵣ val (g ‚ l)));
          rewrite lit_add k1 k2; rewrite mul_distr_l (nth l j) (lit k1) (lit k2);
          refine add_assoc (nth l j *ᵣ lit k1) (nth l j *ᵣ lit k2) (val (g ‚ l)) }
        { assume h;
          change π (val_grp (Var i k1) l ＋ᵣ val ((collect_from (Var j k2) g) ‚ l)
                    = val_grp (Var i k1) l ＋ᵣ val (((Var j k2) ⸬ g) ‚ l));
          rewrite ih (Var j k2); reflexivity }
        { assume h;
          change π (val_grp (Var i k1) l ＋ᵣ val ((collect_from (Var j k2) g) ‚ l)
                    = val_grp (Var i k1) l ＋ᵣ val (((Var j k2) ⸬ g) ‚ l));
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
with remove0 (Cst (cl (0 ‚ _)) ⸬ $l) ↪ remove0 $l
with remove0 (Cst (cl (Zpos $n ‚ $d)) ⸬ $l) ↪ Cst (cl (Zpos $n ‚ $d)) ⸬ remove0 $l
with remove0 (Cst (cl (Zneg $n ‚ $d)) ⸬ $l) ↪ Cst (cl (Zneg $n ‚ $d)) ⸬ remove0 $l
with remove0 (Var _ (cl (0 ‚ _)) ⸬ $l) ↪ remove0 $l
with remove0 (Var $i (cl (Zpos $n ‚ $d)) ⸬ $l) ↪ Var $i (cl (Zpos $n ‚ $d)) ⸬ remove0 $l
with remove0 (Var $i (cl (Zneg $n ‚ $d)) ⸬ $l) ↪ Var $i (cl (Zneg $n ‚ $d)) ⸬ remove0 $l
;

// remove0 on a cons, by cases on the monomial's coefficient
opaque symbol remove0_cons l g xs : π (val ((remove0 (g ⸬ xs)) ‚ l) = val_grp g l ＋ᵣ val ((remove0 xs) ‚ l)) ≔
begin
  assume l;
  induction
  // Cst k
  { induction; induction; induction
    { assume d xs;
      change π (val ((remove0 xs) ‚ l) = lit (cl (0 ‚ d)) ＋ᵣ val ((remove0 xs) ‚ l));
      rewrite lit_zero d; symmetry; refine add_zero_l (val ((remove0 xs) ‚ l)) }
    { assume p d xs; reflexivity }
    { assume p d xs; reflexivity } }
  // Var i k
  { assume i; induction; induction; induction
    { assume d xs;
      change π (val ((remove0 xs) ‚ l) = (nth l i *ᵣ lit (cl (0 ‚ d))) ＋ᵣ val ((remove0 xs) ‚ l));
      rewrite lit_zero d; rewrite mul_zero_r (nth l i);
      symmetry; refine add_zero_l (val ((remove0 xs) ‚ l)) }
    { assume p d xs; reflexivity }
    { assume p d xs; reflexivity } }
end;

opaque symbol remove0_correct l gs : π (val ((remove0 gs) ‚ l) = val (gs ‚ l)) ≔
begin
  assume l;
  induction
  { reflexivity }
  { assume g xs ih; rewrite remove0_cons l g xs; rewrite ih; reflexivity }
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

opaque symbol mul_correct l k g : π (val ((mul k g) ‚ l) = lit k *ᵣ val (g ‚ l)) ≔
begin
  assume l k;
  induction
  { symmetry; refine mul_zero_r (lit k) }
  { induction
    { assume c xs ih;
      change π (lit (k *𝕢 c) ＋ᵣ val ((mul k xs) ‚ l) = lit k *ᵣ (lit c ＋ᵣ val (xs ‚ l)));
      rewrite ih; rewrite lit_mul k c;
      symmetry; refine mul_distr_l (lit k) (lit c) (val (xs ‚ l)) }
    { assume i c xs ih;
      change π ((nth l i *ᵣ lit (k *𝕢 c)) ＋ᵣ val ((mul k xs) ‚ l)
                = lit k *ᵣ ((nth l i *ᵣ lit c) ＋ᵣ val (xs ‚ l)));
      rewrite ih; rewrite lit_mul k c;
      rewrite mul_distr_l (lit k) (nth l i *ᵣ lit c) (val (xs ‚ l));
      rewrite mul_com (lit k) (lit c); rewrite left mul_assoc (nth l i) (lit c) (lit k);
      rewrite mul_com (lit k) (nth l i *ᵣ lit c); reflexivity } }
end;

opaque symbol lin_correct l e : π (val ((lin e) ‚ l) = denote e l) ≔
begin
  assume l;
  induction
  // EAdd
  { assume a ha b hb;
    change π (val ((lin a ++ lin b) ‚ l) = denote a l ＋ᵣ denote b l);
    rewrite ++_eq_+ l (lin a) (lin b); rewrite ha; rewrite hb; reflexivity }
  // EOpp
  { assume a ha;
    change π (val ((mul (—𝕢 1⫽1) (lin a)) ‚ l) = —ᵣ denote a l);
    rewrite mul_correct l (—𝕢 1⫽1) (lin a); rewrite ha; rewrite lit_opp_one;
    rewrite neg_mul one (denote a l); rewrite mul_one_l (denote a l); reflexivity }
  // ECst
  { assume k; refine add_zero_r (lit k) }
  // EMul
  { assume k a ha;
    change π (val ((mul k (lin a)) ‚ l) = lit k *ᵣ denote a l);
    rewrite mul_correct l k (lin a); rewrite ha; reflexivity }
  // EMulr
  { assume a ha k;
    change π (val ((mul k (lin a)) ‚ l) = denote a l *ᵣ lit k);
    rewrite mul_correct l k (lin a); rewrite ha; refine mul_com (lit k) (denote a l) }
  // EAtom
  { assume i;
    change π ((nth l i *ᵣ lit 1⫽1) ＋ᵣ zero = nth l i);
    rewrite add_zero_r (nth l i *ᵣ lit 1⫽1); rewrite lit_one; refine mul_one_r (nth l i) }
end;

opaque symbol reflect e l x : π (denote e l = x) → π (x = val ((norm_speed (lin e)) ‚ l)) ≔
begin
  assume e l x h;
  rewrite norm_correct (lin e) l; rewrite lin_correct l e; symmetry; refine h
end;


symbol l1 x y : π(((lit 2 *ᵣ x) ＋ᵣ y) −ᵣ ((lit 2 *ᵣ x) ＋ᵣ y) ≠ lit 1⫽1) ≔
begin
  assume x y;
  have h : π (((lit 2 *ᵣ x) ＋ᵣ y) −ᵣ ((lit 2 *ᵣ x) ＋ᵣ y) = zero)
  { refine reflect (reify (((lit 2 *ᵣ x) ＋ᵣ y) −ᵣ ((lit 2 *ᵣ x) ＋ᵣ y)) ₁)
                   (reify (((lit 2 *ᵣ x) ＋ᵣ y) −ᵣ ((lit 2 *ᵣ x) ＋ᵣ y)) ₂) _ _;
    reflexivity };
  assume e; refine one≠zero _; rewrite left lit_one; rewrite left e; refine h
end;

opaque symbol lt_imp_le x y : π (x <ᵣ y) → π (x ≤ᵣ y) ≔
begin
  assume x y h; refine ∨ₑ (le_total x y) (λ g, g) (λ g, ⊥ₑ (h g))
end;

opaque symbol pos_ne_zero c : π (zero <ᵣ c) → π (c ≠ zero) ≔
begin
  assume c h e; refine h _; rewrite e; refine le_refl zero
end;

opaque symbol inv_pos c : π (zero <ᵣ c) → π (zero <ᵣ c ⁻¹) ≔
begin
  assume c hc h; refine not_one_le_zero _;
  rewrite left mul_inv_r c (pos_ne_zero c hc); rewrite left mul_zero_r c;
  refine mul_monotone c (c ⁻¹) zero (lt_imp_le zero c hc) h
end;

opaque symbol opp_pos x : π (x <ᵣ zero) → π (zero <ᵣ —ᵣ x) ≔
begin
  assume x hx h; refine hx _;
  rewrite left opp_opp x; rewrite left opp_zero; refine opp_le (—ᵣ x) zero h
end;

// —ᵣ reverses ≤ᵣ, as an equation
opaque symbol opp_le_eq x y : π ((—ᵣ x ≤ᵣ —ᵣ y) = (y ≤ᵣ x)) ≔
begin
  assume x y; refine propExt _ _ _ (opp_le y x);
  assume h; rewrite left opp_opp x; rewrite left opp_opp y; refine opp_le (—ᵣ x) (—ᵣ y) h
end;

// scaling by c > 0 preserves ≤ᵣ
opaque symbol mul_le_eq c : π (zero <ᵣ c) → Π a b, π ((a ≤ᵣ b) = (c *ᵣ a ≤ᵣ c *ᵣ b)) ≔
begin
  assume c hc a b;
  refine propExt _ _ (mul_monotone c a b (lt_imp_le zero c hc)) _;
  assume h;
  rewrite left .[X in X ≤ᵣ _] inv_mul_cancel_l c a (pos_ne_zero c hc);
  rewrite left .[X in _ ≤ᵣ X] inv_mul_cancel_l c b (pos_ne_zero c hc);
  refine mul_monotone (c ⁻¹) (c *ᵣ a) (c *ᵣ b) (lt_imp_le zero (c ⁻¹) (inv_pos c hc)) h
end;

// scaling by c < 0 reverses ≤ᵣ
opaque symbol mul_neg_le_eq c : π (c <ᵣ zero) → Π a b, π ((a ≤ᵣ b) = (c *ᵣ b ≤ᵣ c *ᵣ a)) ≔
begin
  assume c hc a b;
  rewrite mul_le_eq (—ᵣ c) (opp_pos c hc) a b;
  rewrite neg_mul c a; rewrite neg_mul c b;
  refine opp_le_eq (c *ᵣ a) (c *ᵣ b)
end;

// Step 1 of la_generic: negating a literal
opaque symbol Rlt_not_ge n m : π ((n <ᵣ m) = ¬ (n ≥ᵣ m)) ≔
begin
  assume n m; reflexivity
end;

opaque symbol Rle_not_gt n m : π ((n ≤ᵣ m) = ¬ (n >ᵣ m)) ≔
begin
  assume n m; symmetry; refine ¬¬ₑ_eq (n ≤ᵣ m)
end;

opaque symbol Rge_not_lt n m : π ((n ≥ᵣ m) = ¬ (n <ᵣ m)) ≔
begin
  assume n m; symmetry; refine ¬¬ₑ_eq (m ≤ᵣ n)
end;

opaque symbol Rgt_not_le n m : π ((n >ᵣ m) = ¬ (n ≤ᵣ m)) ≔
begin
  assume n m; reflexivity
end;

// Normalising < and ≤ into > and ≥
opaque symbol Rinv_lt_eq a b : π ((a <ᵣ b) = (—ᵣ a >ᵣ —ᵣ b)) ≔
begin
  assume a b; change π (¬ (b ≤ᵣ a) = ¬ (—ᵣ a ≤ᵣ —ᵣ b)); rewrite opp_le_eq a b; reflexivity
end;

opaque symbol Rinv_le_eq a b : π ((a ≤ᵣ b) = (—ᵣ a ≥ᵣ —ᵣ b)) ≔
begin
  assume a b; symmetry; refine opp_le_eq b a
end;

// Moving everything to the left-hand side
opaque symbol R_diff_eq_zero_eq a b : π ((a = b) = (a −ᵣ b = zero)) ≔
begin
  assume a b; refine propExt _ _ _ _
  { assume h; rewrite h; refine add_opp_r b }
  { assume h; rewrite left opp_opp b; refine eq_opp_of_add_zero a (—ᵣ b) h }
end;

opaque symbol R_diff_geq_zero_eq a b : π ((a ≥ᵣ b) = (a −ᵣ b ≥ᵣ zero)) ≔
begin
  assume a b; refine propExt _ _ (sub_nonneg_of_le b a) (le_of_sub_nonneg b a)
end;

opaque symbol R_diff_gt_zero_eq a b : π ((a >ᵣ b) = (a −ᵣ b >ᵣ zero)) ≔
begin
  assume a b; change π (¬ (a ≤ᵣ b) = ¬ (a −ᵣ b ≤ᵣ zero));
  have e : π ((a ≤ᵣ b) = (a −ᵣ b ≤ᵣ zero))
  { refine propExt _ _ _ (le_of_sub_nonpos b a);
    assume h; rewrite left add_opp_r b; refine add_le_mono_r (—ᵣ b) a b h };
  rewrite e; reflexivity
end;

// Scaling a literal by the la_generic coefficient c
opaque symbol Rmult_eq_compat_eq c a b : π (c ≠ zero) → π ((¬ (a = b)) = ¬ (c *ᵣ a = c *ᵣ b)) ≔
begin
  assume c a b hc; apply feq (¬); refine propExt _ _ _ (mul_cancel_l c a b hc);
  assume h; rewrite h; reflexivity
end;

opaque symbol Rmult_gt_compat_eq c a b : π (zero <ᵣ c) → π (¬ (a >ᵣ b) = ¬ (c *ᵣ a >ᵣ c *ᵣ b)) ≔
begin
  assume c a b hc; change π (¬ ¬ (a ≤ᵣ b) = ¬ ¬ (c *ᵣ a ≤ᵣ c *ᵣ b));
  rewrite mul_le_eq c hc a b; reflexivity
end;

opaque symbol Rmult_ge_compat_eq c a b : π (zero <ᵣ c) → π (¬ (a ≥ᵣ b) = ¬ (c *ᵣ a ≥ᵣ c *ᵣ b)) ≔
begin
  assume c a b hc; change π (¬ (b ≤ᵣ a) = ¬ (c *ᵣ b ≤ᵣ c *ᵣ a));
  rewrite mul_le_eq c hc b a; reflexivity
end;

// Side conditions of the scaling lemmas for a literal n / d: the hypothesis
// on the integer n computes to ⊤ for a positive (resp. nonzero) numeral.
opaque symbol of_pos_pos p : π (zero <ᵣ of_pos p) ≔
begin
  assume p h; refine not_one_le_zero (le_tr one (of_pos p) zero (one_le_of_pos p) h)
end;

opaque symbol mul_pos a b : π (zero <ᵣ a) → π (zero <ᵣ b) → π (zero <ᵣ a *ᵣ b) ≔
begin
  assume a b ha hb h; refine hb _;
  have e : π (a *ᵣ b = zero)
  { refine le_antisymmetric (a *ᵣ b) zero h
      (mul_nonneg a b (lt_imp_le zero a ha) (lt_imp_le zero b hb)) };
  rewrite left inv_mul_cancel_l a b (pos_ne_zero a ha); rewrite e; rewrite mul_zero_r (a ⁻¹);
  refine le_refl zero
end;

opaque symbol lit_pos n d : π (0 < n) → π (zero <ᵣ lit (n / d)) ≔
begin
  induction
  { assume d h; refine ⊥ₑ h }
  { assume p d h; rewrite lit_def;
    refine mul_pos (of_pos p) ((of_pos d) ⁻¹) (of_pos_pos p) (inv_pos (of_pos d) (of_pos_pos d)) }
  { assume p d h; refine ⊥ₑ h }
end;

opaque symbol of_int_ne_zero n : π (istrue (not (isEq (n ≐ 0)))) → π (of_int n ≠ zero) ≔
begin
  induction
  { assume h; refine ⊥ₑ h }
  { assume p h; refine of_pos≠zero p }
  { assume p h; change π ((—ᵣ (of_pos p) = zero) ⇒ ⊥); assume e; refine of_pos≠zero p _;
    rewrite left opp_opp (of_pos p); rewrite e; refine opp_zero }
end;

opaque symbol lit_ne_zero n d : π (istrue (not (isEq (n ≐ 0)))) → π (lit (n / d) ≠ zero) ≔
begin
  assume n d hn; rewrite lit_def; assume e;
  refine of_int_ne_zero n hn _;
  rewrite left mul_inv_cancel (of_pos d) (of_int n) (of_pos≠zero d);
  rewrite left mul_zero_r (of_pos d); rewrite left e; reflexivity
end;

// Summing the scaled literals
opaque symbol Rsum_geq_s a b c d : π (a ≥ᵣ b) → π (c ≥ᵣ d) → π (a ＋ᵣ c ≥ᵣ b ＋ᵣ d) ≔
begin
  assume a b c d hab hcd; refine add_le_mono b a d c hab hcd
end;

opaque symbol Rsum_gt_ge a b c d : π (a >ᵣ b) → π (c ≥ᵣ d) → π (a ＋ᵣ c >ᵣ b ＋ᵣ d) ≔
begin
  assume a b c d hab hcd h; refine hab (add_le_cancel_l c a b _);
  rewrite add_com c a; rewrite add_com c b;
  refine le_tr (a ＋ᵣ c) (b ＋ᵣ d) (b ＋ᵣ c) h (add_monotone b d c hcd)
end;

opaque symbol Rsum_ge_gt a b c d : π (a ≥ᵣ b) → π (c >ᵣ d) → π (a ＋ᵣ c >ᵣ b ＋ᵣ d) ≔
begin
  assume a b c d hab hcd; rewrite add_com a c; rewrite add_com b d; refine Rsum_gt_ge c d a b hcd hab
end;

opaque symbol Rsum_gt_gt a b c d : π (a >ᵣ b) → π (c >ᵣ d) → π (a ＋ᵣ c >ᵣ b ＋ᵣ d) ≔
begin
  assume a b c d hab hcd; refine Rsum_gt_ge a b c d hab (lt_imp_le d c hcd)
end;

/* ------------------------------------------------------------------------
   la_generic, the tail. The script rules/lra.rs generates keeps `zero` on
   the right of every scaled literal, sums them into `l ⋈ zero`, rewrites `l`
   into its normal form with `reflect (reify l ₁) (reify l ₂) l (eq_refl l)` --
   the premise holds by computation on the concrete `l`, so no lemma reduces
   `rfy` on a variable -- and closes by deciding the sign of that normal form
   by computation: over the reals `≤ᵣ` does not compute, so the `refine ⊤ᵢ`
   that closes `l < r` on ℤ in lia.lp has no counterpart here.
   ------------------------------------------------------------------------ */

// Scaling, with `zero` kept on the right-hand side.
opaque symbol Rmult_eq_compat_zero_eq c a : π (c ≠ zero) → π ((¬ (a = zero)) = ¬ (c *ᵣ a = zero)) ≔
begin
  assume c a hc; rewrite Rmult_eq_compat_eq c a zero hc; rewrite mul_zero_r c; reflexivity
end;

opaque symbol Rmult_ge_compat_zero_eq c a : π (zero <ᵣ c) → π (¬ (a ≥ᵣ zero) = ¬ (c *ᵣ a ≥ᵣ zero)) ≔
begin
  assume c a hc; rewrite Rmult_ge_compat_eq c a zero hc; rewrite mul_zero_r c; reflexivity
end;

opaque symbol Rmult_gt_compat_zero_eq c a : π (zero <ᵣ c) → π (¬ (a >ᵣ zero) = ¬ (c *ᵣ a >ᵣ zero)) ≔
begin
  assume c a hc; rewrite Rmult_gt_compat_eq c a zero hc; rewrite mul_zero_r c; reflexivity
end;

// An equality literal, weakened to the inequality the sum needs.
opaque symbol R_eq_ge a : π (a = zero) → π (a ≥ᵣ zero) ≔
begin
  assume a h; rewrite h; refine le_reflexive zero
end;

// Summing, with `zero` kept on the right-hand side.
opaque symbol Rsum0_ge_ge a c : π (a ≥ᵣ zero) → π (c ≥ᵣ zero) → π (a ＋ᵣ c ≥ᵣ zero) ≔
begin
  assume a c ha hc;
  refine le_tr zero (zero ＋ᵣ zero) (a ＋ᵣ c) _ (Rsum_geq_s a zero c zero ha hc);
  rewrite add_zero_r zero; refine le_reflexive zero
end;

opaque symbol Rsum0_gt_ge a c : π (a >ᵣ zero) → π (c ≥ᵣ zero) → π (a ＋ᵣ c >ᵣ zero) ≔
begin
  assume a c ha hc h; refine Rsum_gt_ge a zero c zero ha hc _; rewrite add_zero_r zero; refine h
end;

opaque symbol Rsum0_ge_gt a c : π (a ≥ᵣ zero) → π (c >ᵣ zero) → π (a ＋ᵣ c >ᵣ zero) ≔
begin
  assume a c ha hc h; refine Rsum_ge_gt a zero c zero ha hc _; rewrite add_zero_r zero; refine h
end;

opaque symbol Rsum0_gt_gt a c : π (a >ᵣ zero) → π (c >ᵣ zero) → π (a ＋ᵣ c >ᵣ zero) ≔
begin
  assume a c ha hc h; refine Rsum_gt_gt a zero c zero ha hc _; rewrite add_zero_r zero; refine h
end;

// The summed literal against its own negation.
opaque symbol Rge_lt_absurd l : π (l <ᵣ zero) → π (l ≥ᵣ zero) → π ⊥ ≔
begin
  assume l h g; refine h g
end;

opaque symbol Rgt_le_absurd l : π (l ≤ᵣ zero) → π (l >ᵣ zero) → π ⊥ ≔
begin
  assume l h g; refine g h
end;

// The sign of a normal form that is one constant, or nothing at all. No
// catch-all: a sequential one would also fire on a neutral term.
symbol cst_neg : 𝕃 grp → 𝔹;
rule cst_neg □ ↪ false
with cst_neg (_ ⸬ (_ ⸬ _)) ↪ false
with cst_neg (Var _ _ ⸬ □) ↪ false
with cst_neg (Cst (cl (Z0 ‚ _)) ⸬ □) ↪ false
with cst_neg (Cst (cl (Zpos _ ‚ _)) ⸬ □) ↪ false
with cst_neg (Cst (cl (Zneg _ ‚ _)) ⸬ □) ↪ true;

symbol cst_nonpos : 𝕃 grp → 𝔹;
rule cst_nonpos □ ↪ true
with cst_nonpos (_ ⸬ (_ ⸬ _)) ↪ false
with cst_nonpos (Var _ _ ⸬ □) ↪ false
with cst_nonpos (Cst (cl (Z0 ‚ _)) ⸬ □) ↪ true
with cst_nonpos (Cst (cl (Zpos _ ‚ _)) ⸬ □) ↪ false
with cst_nonpos (Cst (cl (Zneg _ ‚ _)) ⸬ □) ↪ true;

opaque symbol lit_neg_lt_zero p d : π (lit (Zneg p / d) <ᵣ zero) ≔
begin
  assume p d h;
  refine lit_pos (Zpos p) d ⊤ᵢ _;
  have e : π (lit (Zpos p / d) = —ᵣ lit (Zneg p / d))
  { rewrite lit_def (Zpos p / d); rewrite lit_def (Zneg p / d);
    change π (of_pos p *ᵣ (of_pos d) ⁻¹ = —ᵣ ((—ᵣ of_pos p) *ᵣ (of_pos d) ⁻¹));
    rewrite neg_mul (of_pos p) ((of_pos d) ⁻¹);
    rewrite opp_opp (of_pos p *ᵣ (of_pos d) ⁻¹); reflexivity };
  rewrite e; refine opp_nonpos_of_nonneg (lit (Zneg p / d)) h
end;

opaque symbol val_lt_zero g env : π (istrue (cst_neg g)) → π (val (g ‚ env) <ᵣ zero) ≔
begin
  assume g env;
  refine case_𝕃2 (λ g, istrue (cst_neg g) ⇒ val (g ‚ env) <ᵣ zero) _ _ _ g
  { assume h; refine ⊥ₑ h }
  { induction
    { induction; induction; induction
      { assume d h; refine ⊥ₑ h }
      { assume p d h; refine ⊥ₑ h }
      { assume p d h;
        change π (lit (Zneg p / d) ＋ᵣ zero <ᵣ zero);
        rewrite add_zero_r (lit (Zneg p / d)); refine lit_neg_lt_zero p d } }
    { assume i q h; refine ⊥ₑ h } }
  { assume x y l h; refine ⊥ₑ h }
end;

opaque symbol val_le_zero g env : π (istrue (cst_nonpos g)) → π (val (g ‚ env) ≤ᵣ zero) ≔
begin
  assume g env;
  refine case_𝕃2 (λ g, istrue (cst_nonpos g) ⇒ val (g ‚ env) ≤ᵣ zero) _ _ _ g
  { assume h; refine le_reflexive zero }
  { induction
    { induction; induction; induction
      { assume d h;
        change π (lit (cl (Z0 ‚ d)) ＋ᵣ zero ≤ᵣ zero);
        rewrite add_zero_r (lit (cl (Z0 ‚ d))); rewrite lit_zero d; refine le_reflexive zero }
      { assume p d h; refine ⊥ₑ h }
      { assume p d h;
        change π (lit (Zneg p / d) ＋ᵣ zero ≤ᵣ zero);
        rewrite add_zero_r (lit (Zneg p / d));
        refine lt_imp_le (lit (Zneg p / d)) zero (lit_neg_lt_zero p d) } }
    { assume i q h; refine ⊥ₑ h } }
  { assume x y l h; refine ⊥ₑ h }
end;

/* ------------------------------------------------------------------------
   la_mult_neg: multiplying both sides by a negative t1 flips the relation
   ------------------------------------------------------------------------ */

opaque symbol la_mult_neg_eq [t1 t2 t3] : π ((t1 <ᵣ zero) ⇒ (t2 = t3) ⇒ (t1 *ᵣ t2) = (t1 *ᵣ t3)) ≔
begin
  assume t1 t2 t3 hc h; rewrite h; reflexivity
end;

opaque symbol la_mult_neg_lt t1 t2 t3 : π (t1 <ᵣ zero) → π (t2 <ᵣ t3) → π ((t1 *ᵣ t2) >ᵣ (t1 *ᵣ t3)) ≔
begin
  assume t1 t2 t3 hc h; change π (¬ (t1 *ᵣ t2 ≤ᵣ t1 *ᵣ t3));
  rewrite left mul_neg_le_eq t1 hc t3 t2; refine h
end;

opaque symbol la_mult_neg_leq [t1 t2 t3] : π ((t1 <ᵣ zero) ⇒ (t2 ≤ᵣ t3) ⇒ (t1 *ᵣ t2) ≥ᵣ (t1 *ᵣ t3)) ≔
begin
  assume t1 t2 t3 hc h; change π (t1 *ᵣ t3 ≤ᵣ t1 *ᵣ t2);
  rewrite left mul_neg_le_eq t1 hc t2 t3; refine h
end;

opaque symbol la_mult_neg_gt [t1 t2 t3] : π ((t1 <ᵣ zero) ⇒ (t2 >ᵣ t3) ⇒ (t1 *ᵣ t2) <ᵣ (t1 *ᵣ t3)) ≔
begin
  assume t1 t2 t3 hc h; change π (¬ (t1 *ᵣ t3 ≤ᵣ t1 *ᵣ t2));
  rewrite left mul_neg_le_eq t1 hc t2 t3; refine h
end;

opaque symbol la_mult_neg_ge [t1 t2 t3] : π ((t1 <ᵣ zero) ⇒ (t2 ≥ᵣ t3) ⇒ (t1 *ᵣ t2) ≤ᵣ (t1 *ᵣ t3)) ≔
begin
  assume t1 t2 t3 hc h; rewrite left mul_neg_le_eq t1 hc t3 t2; refine h
end;

/*
  The Alethe la_* rules
*/

require open alethe.core;

opaque symbol la_disequality (t1 t2: τ real) : π̇ (((t1 = t2) ∨ ¬ (t1 ≤ᵣ t2) ∨ ¬ (t2 ≤ᵣ t1)) ⸬ □) ≔
begin
  assume t1 t2;
  apply ∨ᵢ₁;
  rewrite ∨_com;
  rewrite ∨_assoc;
  rewrite imp_eq_or;
  rewrite imp_eq_or;
  refine le_antisymmetric t1 t2
end;

opaque symbol la_totality (t1 t2: τ real) : π̇ (((t1 ≤ᵣ t2) ∨ (t2 ≤ᵣ t1)) ⸬ □) ≔
begin
  assume t1 t2;
  apply ∨ᵢ₁;
  refine le_total t1 t2
end;
