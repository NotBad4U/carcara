// cvc5 RARE rewrites over Booleans and equality. A `rare_rewrite` step cites a
// lemma here by the RARE rule's name, so each lemma keeps that name verbatim.
// Opened with alethe.prop.
require open alethe.core alethe.prop;
require open Stdlib.List;

opaque symbol eq-refl [a] (t: τ a) : π ((t = t) = ⊤) ≔ begin
    assume a p;
    apply prop_ext;
    apply ∧ᵢ
    { assume H; remove H; apply ⊤ᵢ  }
    { assume H⊤; remove H⊤; reflexivity } 
end;

// (define-rule eq-symm ((t ?) (s ?)) (= t s) (= s t))
opaque symbol eq-symm [a] (t s: τ a) : π ((t = s) = (s = t)) ≔
begin
    assume a t s;
    apply prop_ext;
    apply ∧ᵢ
    {
        assume H;
        symmetry; apply H
    }
    {
        assume H;
        symmetry; apply H
    }
end;

// (define-rule bool-impl-false1 ((t Bool)) (=> t false) (not t))
opaque symbol bool-impl-false1 t : π ((t ⇒ ⊥) = ¬ t) ≔ implies_simplify5 t;

// (define-rule bool-impl-false2 ((t Bool)) (=> false t) true)
opaque symbol bool-impl-false2 t : π ((⊥ ⇒ t) = ⊤) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    { assume Htbot; apply ⊤ᵢ  }
    { assume Htop;  assume Ht; apply ⊥ₑ Ht }
end;

// (define-rule bool-double-not-elim ((t Bool)) (not (not t)) t)
// Duplicate of Alethe
opaque symbol bool-double-not-elim t : π ((¬ (¬ t)) = t) ≔ not_simplify1 t;


//(define-rule bool-impl-elim ((t Bool) (s Bool)) (=> t s) (or (not t) s))
opaque symbol bool-impl-elim s t: π ((s ⇒ t) = ((¬ s) ∨ t)) ≔
begin
  assume s t;
  apply prop_ext;
  apply ∧ᵢ
  {  assume Himp; apply imply_to_or Himp }
  {  assume Hor; refine or_to_imply Hor }
end;

//(define-rule distinct-binary-elim ((t ?) (s ?)) (distinct t s) (not (= t s)))
opaque symbol distinct-binary-elim [a] (t s: τ a) : π (distinct (cons t (cons s ⧈)) = ( t ≠ s)) ≔ eq_refl (distinct (cons t (cons s ⧈)));

// (define-rule bool-impl-true2 ((t Bool)) (=> true t) t)
opaque symbol bool-impl-true2 t : π ((⊤ ⇒ t) = t) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    {   assume HTopt; apply HTopt ⊤ᵢ }
    {  assume Ht;  assume Htop; apply Ht }
end;

// (define-rule bool-impl-true1 ((t Bool)) (=> t true) true)
opaque symbol bool-impl-true1 t : π ((t ⇒ ⊤) = ⊤) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    {   assume HTopt; apply ⊤ᵢ }
    {  assume Ht;  assume Htop; apply ⊤ᵢ }
end;


// (define-rule* bool-and-true ((xs Bool :list) (ys Bool :list)) (and xs true ys) (and xs ys))
opaque symbol bool-and-true xs ys : π ((xs ∧ ⊤ ∧ ys) = (xs ∧ ys)) ≔
begin
    assume xs ys;
    rewrite ∧_com ⊤ ys;
    rewrite and_identity_r;
    reflexivity
end;

// (define-rule bool-and-false ((xs Bool :list) (ys Bool :list)) (and xs false ys) false)
opaque symbol bool-and-false xs ys : π ((xs ∧ ⊥ ∧ ys) = ⊥) ≔
begin
    assume xs ys;
    rewrite ∧_com ⊥ ys;
    rewrite and_domination;
    rewrite and_domination;
    reflexivity
end;

// (define-rule* bool-or-false ((xs Bool :list) (ys Bool :list)) (or xs false ys) (or xs ys))
opaque symbol bool-or-false xs ys : π ((xs ∨ ⊥ ∨ ys) = (xs ∨ ys)) ≔
begin
    assume xs ys; 
    rewrite ∨_com ⊥ ys;
    rewrite or_identity_r;
    reflexivity
end;

// (define-rule* bool-or-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list)) (or xs (or b ys) zs) (or xs b ys zs))
opaque symbol bool-or-flatten xs b ys zs : π ((xs ∨ (b ∨ ys) ∨ zs) = (xs ∨ b ∨ ys ∨ zs)) ≔
begin
    assume xs b ys zs;
    rewrite ∨_assoc;
    reflexivity
end;


// Reviewed bool-or-flatten without `xs`
// (define-rule* bool-or-flatten ((b Bool) (ys Bool :list) (zs Bool :list)) (or (or b ys) zs) (or b ys zs))
opaque symbol bool-or-flatten' b ys zs : π (((b ∨ ys) ∨ zs) = (b ∨ ys ∨ zs)) ≔
begin
    assume b ys zs;
    apply ∨_assoc;
end;

// (define-rule* bool-and-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list)) (and xs (and b ys) zs) (and xs b ys zs))
opaque symbol bool-and-flatten b [xs ys zs] : π ((xs ∧ (b ∧ ys) ∧ zs) = (xs ∧ b ∧ ys ∧ zs)) ≔
begin
    assume b xs ys zs;
    rewrite ∧_assoc;
    reflexivity
end;

// Reviewed bool-and-flatten without `xs`
// (define-rule* bool-and-flatten ((b Bool) (ys Bool :list) (zs Bool :list)) (and (and b ys) zs) (and b ys zs))
opaque symbol bool-and-flatten' b ys zs : π (((b ∧ ys) ∧ zs) = (b ∧ ys ∧ zs)) ≔
begin
    assume b ys zs;
    apply ∧_assoc;
end;

// (define-rule bool-eq-true ((t Bool)) (= t true) t)
opaque symbol bool-eq-true (t: τ o) : π ((t = ⊤) = t) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    {
        
        assume H;
        rewrite H;
        apply ⊤ᵢ
    }
    {
        
        assume Ht;
        apply prop_ext;
        apply ∧ᵢ
        {  assume Ht'; apply ⊤ᵢ }
        {  assume Ht';  apply Ht }
    }
end;

// (define-rule bool-eq-false ((t Bool)) (= t false) (not t))
opaque symbol bool-eq-false (t: τ o) : π ((t = ⊥) = ¬ t) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    {
        
        assume H;
        rewrite H;
        assume Hbot;
        apply Hbot
    }
    {
        
        assume Hnt;
        apply prop_ext;
        apply ∧ᵢ
        {   assume Ht; apply (¬ₑ Hnt Ht) }
        {  assume Ht';  apply (⊥ₑ Ht') }
    }
end;

// (define-rule* bool-and-de-morgan ((x Bool) (y Bool) (zs Bool :list)) 
//   (not (and x y zs))
//   (not (and y zs))
//   (or (not x) _))
opaque symbol bool-and-de-morgan (x y zs: τ o): π ((¬ (x ∧ y ∧ zs)) = ((¬ x) ∨ (¬ y) ∨ (¬ zs))) ≔
begin
    assume x y zs;
    apply prop_ext;
    apply ∧ᵢ
    { rewrite morgan1; rewrite morgan1;  assume H; refine H }
    { rewrite morgan1; rewrite morgan1;  assume H; refine H }
end;

// (define-rule* bool-or-de-morgan ((x Bool) (y Bool) (zs Bool :list)) 
//   (not (or x y zs))
//   (not (or y zs))
//   (and (not x) _))
opaque symbol bool-or-de-morgan (x y zs: τ o): π ((¬ (x ∨ y ∨ zs)) = ((¬ x) ∧ (¬ y) ∧ (¬ zs))) ≔
begin
    assume x y zs;
    apply prop_ext;
    apply ∧ᵢ
    { rewrite morgan2; rewrite morgan2;  assume H; refine H }
    { rewrite morgan2; rewrite morgan2;  assume H; refine H }
end;


// Integer
opaque symbol bool_implies_or_distrib (y1 y2 z: τ o) : π (((y1 ∨ y2) ⇒ z) = ((y1 ⇒ z) ∧ (y2 ⇒ z))) ≔
begin
    assume y1 y2 z;
    apply prop_ext;
    apply ∧ᵢ
    {
        assume H;
        apply ∧ᵢ
        { assume H1; refine H (∨ᵢ₁ H1) }
        { assume H2; refine H (∨ᵢ₂ H2) }
    }
    {
        assume H H1;
        apply ∨ₑ H1
        { assume H2; refine (∧ₑ₁ H) H2 }
        { assume Hy; refine (∧ₑ₂ H) Hy }
    }
end;

//  (define-rule* bool-implies-or-distrib
//  ((y1 Bool) (y2 Bool) (ys Bool :list) (z Bool))
//      (=> (or y1 y2 ys) z)
//      (=> (or y2 ys) z)
//      (and (=> y1 z) _))
// Version with list of disjuncts `ys`
opaque symbol bool_implies_or_distrib_rec (y1 y2 ys z: τ o) : π (((y1 ∨ y2 ∨ ys) ⇒ z) = ((y1 ⇒ z) ∧ (y2 ∨ ys ⇒ z))) ≔
begin
    assume y1 y2 ys z;
    refine bool_implies_or_distrib y1 (y2 ∨ ys) z;
end;

opaque symbol ite-eq (c: τ o) [a] (x y: τ a) : π ((ite c ((ite c x y) = x) ((ite c x y) = y)) = ⊤) ≔
begin
  assume c a x y;
  apply prop_ext;
  apply ∧ᵢ
  { assume H; apply ⊤ᵢ }
  { assume Htop;
    refine ite_ind c ((ite c x y) = x) ((ite c x y) = y) (λ u, u) _ _
    { assume hc;
      refine ite_ind c x y (λ u, u = x) _ _
      { assume hc2; reflexivity }
      { assume hnc; refine ⊥ₑ (hnc hc) } }
    { assume hnc;
      refine ite_ind c x y (λ u, u = y) _ _
      { assume hc; refine ⊥ₑ (hnc hc) }
      { assume hc2; reflexivity } } }
end;

/* ------------------------------------------------------------------------
   Case analysis on Booleans
   ------------------------------------------------------------------------ */

// A proved formula is `⊤`, a refuted one `⊥`. `rewrite (eq_⊤ᵢ h)` replaces the
// variable `h` proves by `⊤`, which is how the lemmas below split on a Boolean.
opaque symbol eq_⊤ᵢ [p] : π p → π (p = ⊤) ≔
begin
    assume p h;
    apply prop_ext;
    apply ∧ᵢ
    { assume h1; apply ⊤ᵢ }
    { assume h1; refine h }
end;

opaque symbol eq_⊥ᵢ [p] : π (¬ p) → π (p = ⊥) ≔
begin
    assume p h;
    apply prop_ext;
    apply ∧ᵢ
    { assume h1; refine h h1 }
    { assume h1; refine ⊥ₑ h1 }
end;

// Folds the Boolean constants a case split leaves behind, then closes the goal.
symbol bool_eval_rules ≔
    (#rewrite ¬⊤) ⸬ (#rewrite ¬⊥) ⸬ (#rewrite ¬¬ₑ_eq)
    ⸬ (#rewrite ∧⊤) ⸬ (#rewrite ⊤∧) ⸬ (#rewrite ∧⊥) ⸬ (#rewrite ⊥∧)
    ⸬ (#rewrite ∨⊤) ⸬ (#rewrite ⊤∨) ⸬ (#rewrite ∨⊥) ⸬ (#rewrite ⊥∨)
    ⸬ (#rewrite ⊤⇒) ⸬ (#rewrite ⇒⊤) ⸬ (#rewrite ⊥⇒)
    ⸬ (#rewrite ⊤=) ⸬ (#rewrite =⊤) ⸬ (#rewrite ⊥=) ⸬ (#rewrite =⊥)
    ⸬ (#rewrite (ite_simplify1 o)) ⸬ (#rewrite (ite_simplify2 o))
    ⸬ □;

symbol bool_eval ≔ #repeat (applyAny bool_eval_rules) and #try (#reflexivity #orelse (#apply ⊤ᵢ));

/* ------------------------------------------------------------------------
   cvc5 RARE Boolean rewrites (theory/booleans/rewrites)
   A `define-cond-rule` lemma takes its condition as a hypothesis after its
   variables; the translator discharges it with the step's premise.
   ------------------------------------------------------------------------ */

// (define-cond-rule bool-not-true ((t Bool)) (= t false) (not t) true)
opaque symbol bool-not-true (t: τ o) : π (t = ⊥) → π ((¬ t) = ⊤) ≔
begin assume t h; rewrite h; eval bool_eval end;

// (define-cond-rule bool-not-false ((t Bool)) (= t true) (not t) false)
opaque symbol bool-not-false (t: τ o) : π (t = ⊤) → π ((¬ t) = ⊥) ≔
begin assume t h; rewrite h; eval bool_eval end;

// (define-rule bool-eq-nrefl ((x Bool)) (= x (not x)) false)
opaque symbol bool-eq-nrefl (x: τ o) : π ((x = (¬ x)) = ⊥) ≔ equiv_simplify3 x;

// (define-rule bool-dual-impl-eq ((t Bool) (s Bool)) (and (=> t s) (=> s t)) (= t s))
opaque symbol bool-dual-impl-eq (t s: τ o) : π (((t ⇒ s) ∧ (s ⇒ t)) = (t = s)) ≔ iff_equiv_eq t s;

// (define-rule bool-implies-de-morgan ((x Bool) (y Bool)) (not (=> x y)) (and x (not y)))
opaque symbol bool-implies-de-morgan (x y: τ o) : π ((¬ (x ⇒ y)) = (x ∧ (¬ y))) ≔ ¬⇒=∧¬ x y;

// (define-rule* bool-or-and-distrib ((y1 Bool) (y2 Bool) (ys Bool :list) (z1 Bool) (zs Bool :list))
//   (or (and y1 y2 ys) z1 zs)
//   (or (and y2 ys) z1 zs)
//   (and (or y1 z1 zs) _))
// One unfolding, with `y2` standing for `(and y2 ys)` and `z` for `(or z1 zs)`.
// The translator repeats it to the fixed point.
opaque symbol bool-or-and-distrib (y1 y2 z: τ o) : π (((y1 ∧ y2) ∨ z) = ((y1 ∨ z) ∧ (y2 ∨ z))) ≔
    ∧∨_dist_l y1 y2 z;

// (define-rule bool-xor-refl ((x Bool)) (xor x x) false)
opaque symbol bool-xor-refl (x: τ o) : π ((xor x x) = ⊥) ≔
begin
    assume x; simplify xor;
    apply ∨ₑ (em x)
    { assume h; rewrite (eq_⊤ᵢ h); eval bool_eval }
    { assume h; rewrite (eq_⊥ᵢ h); eval bool_eval }
end;

// (define-rule bool-xor-nrefl ((x Bool)) (xor x (not x)) true)
opaque symbol bool-xor-nrefl (x: τ o) : π ((xor x (¬ x)) = ⊤) ≔
begin
    assume x; simplify xor;
    apply ∨ₑ (em x)
    { assume h; rewrite (eq_⊤ᵢ h); eval bool_eval }
    { assume h; rewrite (eq_⊥ᵢ h); eval bool_eval }
end;

// (define-rule bool-xor-false ((x Bool)) (xor x false) x)
opaque symbol bool-xor-false (x: τ o) : π ((xor x ⊥) = x) ≔
begin
    assume x; simplify xor;
    apply ∨ₑ (em x)
    { assume h; rewrite (eq_⊤ᵢ h); eval bool_eval }
    { assume h; rewrite (eq_⊥ᵢ h); eval bool_eval }
end;

// (define-rule bool-xor-true ((x Bool)) (xor x true) (not x))
opaque symbol bool-xor-true (x: τ o) : π ((xor x ⊤) = (¬ x)) ≔
begin
    assume x; simplify xor;
    apply ∨ₑ (em x)
    { assume h; rewrite (eq_⊤ᵢ h); eval bool_eval }
    { assume h; rewrite (eq_⊥ᵢ h); eval bool_eval }
end;

// (define-rule bool-xor-comm ((x Bool) (y Bool)) (xor x y) (xor y x))
opaque symbol bool-xor-comm (x y: τ o) : π ((xor x y) = (xor y x)) ≔
begin
    assume x y; simplify xor;
    apply ∨ₑ (em x)
    { assume h; rewrite (eq_⊤ᵢ h); eval bool_eval }
    { assume h; rewrite (eq_⊥ᵢ h); eval bool_eval }
end;

// (define-rule bool-xor-elim ((x Bool) (y Bool)) (xor x y) (= (not x) y))
opaque symbol bool-xor-elim (x y: τ o) : π ((xor x y) = ((¬ x) = y)) ≔
begin
    assume x y; simplify xor;
    apply ∨ₑ (em x)
    { assume h; rewrite (eq_⊤ᵢ h); eval bool_eval }
    { assume h; rewrite (eq_⊥ᵢ h); eval bool_eval }
end;

// (define-rule bool-not-xor-elim ((x Bool) (y Bool)) (not (xor x y)) (= x y))
opaque symbol bool-not-xor-elim (x y: τ o) : π ((¬ (xor x y)) = (x = y)) ≔
begin
    assume x y; simplify xor;
    apply ∨ₑ (em x)
    { assume h; rewrite (eq_⊤ᵢ h); eval bool_eval }
    { assume h; rewrite (eq_⊥ᵢ h); eval bool_eval }
end;

// (define-rule bool-not-eq-elim1 ((x Bool) (y Bool)) (not (= x y)) (= (not x) y))
opaque symbol bool-not-eq-elim1 (x y: τ o) : π ((¬ (x = y)) = ((¬ x) = y)) ≔
begin
    assume x y;
    apply ∨ₑ (em x)
    { assume h; rewrite (eq_⊤ᵢ h); eval bool_eval }
    { assume h; rewrite (eq_⊥ᵢ h); eval bool_eval }
end;

// (define-rule bool-not-eq-elim2 ((x Bool) (y Bool)) (not (= x y)) (= x (not y)))
opaque symbol bool-not-eq-elim2 (x y: τ o) : π ((¬ (x = y)) = (x = (¬ y))) ≔
begin
    assume x y;
    apply ∨ₑ (em x)
    { assume h; rewrite (eq_⊤ᵢ h); eval bool_eval }
    { assume h; rewrite (eq_⊥ᵢ h); eval bool_eval }
end;

// (define-cond-rule ite-neg-branch ((c Bool) (x Bool) (y Bool)) (= (not y) x) (ite c x y) (= c x))
opaque symbol ite-neg-branch (c x y: τ o) : π ((¬ y) = x) → π ((ite c x y) = (c = x)) ≔
begin
    assume c x y h;
    rewrite left h;
    apply ∨ₑ (em c)
    { assume hc; rewrite (eq_⊤ᵢ hc); eval bool_eval }
    { assume hc; rewrite (eq_⊥ᵢ hc); eval bool_eval }
end;

// (define-rule ite-then-true ((c Bool) (x Bool)) (ite c true x) (or c x))
opaque symbol ite-then-true (c x: τ o) : π ((ite c ⊤ x) = (c ∨ x)) ≔ ite_simplify9 c x;

// (define-rule ite-else-false ((c Bool) (x Bool)) (ite c x false) (and c x))
opaque symbol ite-else-false (c x: τ o) : π ((ite c x ⊥) = (c ∧ x)) ≔ ite_simplify10 c x;

// (define-rule ite-then-false ((c Bool) (x Bool)) (ite c false x) (and (not c) x))
opaque symbol ite-then-false (c x: τ o) : π ((ite c ⊥ x) = ((¬ c) ∧ x)) ≔ ite_simplify11 c x;

// (define-rule ite-else-true ((c Bool) (x Bool)) (ite c x true) (or (not c) x))
opaque symbol ite-else-true (c x: τ o) : π ((ite c x ⊤) = ((¬ c) ∨ x)) ≔ ite_simplify12 c x;

// (define-rule ite-then-lookahead-self ((c Bool) (x Bool)) (ite c c x) (ite c true x))
opaque symbol ite-then-lookahead-self (c x: τ o) : π ((ite c c x) = (ite c ⊤ x)) ≔
begin
    assume c x;
    apply ∨ₑ (em c)
    { assume h; rewrite (eq_⊤ᵢ h); eval bool_eval }
    { assume h; rewrite (eq_⊥ᵢ h); eval bool_eval }
end;

// (define-rule ite-else-lookahead-self ((c Bool) (x Bool)) (ite c x c) (ite c x false))
opaque symbol ite-else-lookahead-self (c x: τ o) : π ((ite c x c) = (ite c x ⊥)) ≔
begin
    assume c x;
    apply ∨ₑ (em c)
    { assume h; rewrite (eq_⊤ᵢ h); eval bool_eval }
    { assume h; rewrite (eq_⊥ᵢ h); eval bool_eval }
end;

// (define-rule ite-then-lookahead-not-self ((c Bool) (x Bool)) (ite c (not c) x) (ite c false x))
opaque symbol ite-then-lookahead-not-self (c x: τ o) : π ((ite c (¬ c) x) = (ite c ⊥ x)) ≔
begin
    assume c x;
    apply ∨ₑ (em c)
    { assume h; rewrite (eq_⊤ᵢ h); eval bool_eval }
    { assume h; rewrite (eq_⊥ᵢ h); eval bool_eval }
end;

// (define-rule ite-else-lookahead-not-self ((c Bool) (x Bool)) (ite c x (not c)) (ite c x true))
opaque symbol ite-else-lookahead-not-self (c x: τ o) : π ((ite c x (¬ c)) = (ite c x ⊤)) ≔
begin
    assume c x;
    apply ∨ₑ (em c)
    { assume h; rewrite (eq_⊤ᵢ h); eval bool_eval }
    { assume h; rewrite (eq_⊥ᵢ h); eval bool_eval }
end;

// (define-rule ite-expand ((c Bool) (x Bool) (y Bool)) (ite c x y) (and (or (not c) x) (or c y)))
opaque symbol ite-expand (c x y: τ o) : π ((ite c x y) = (((¬ c) ∨ x) ∧ (c ∨ y))) ≔
begin
    assume c x y;
    apply ∨ₑ (em c)
    { assume h; rewrite (eq_⊤ᵢ h); eval bool_eval }
    { assume h; rewrite (eq_⊥ᵢ h); eval bool_eval }
end;

// (define-rule bool-not-ite-elim ((c Bool) (x Bool) (y Bool)) (not (ite c x y)) (ite c (not x) (not y)))
opaque symbol bool-not-ite-elim (c x y: τ o) : π ((¬ (ite c x y)) = (ite c (¬ x) (¬ y))) ≔
begin
    assume c x y;
    apply ∨ₑ (em c)
    { assume h; rewrite (eq_⊤ᵢ h); eval bool_eval }
    { assume h; rewrite (eq_⊥ᵢ h); eval bool_eval }
end;
