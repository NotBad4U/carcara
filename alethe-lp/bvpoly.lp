/*
  cvc5's `poly_simp` and `poly_simp_rel` over bit-vectors, by reflection.

  A bit-vector term built from `bvadd bvsub bvneg`, multiplication by a
  literal and literals is reified (`brfy`, by rewriting, atoms numbered in an
  environment) into the syntax `BExpr`, whose denotation `bdenote` is the term
  again by conversion. `blin n` computes a canonical linear form — a list of
  monomials (coefficient, atom index) sorted by index, coefficients and the
  constant reduced modulo 2ⁿ, zero coefficients dropped — and `blin_correct`
  proves that its value `bval` is the denotation. Two terms whose linear forms
  are convertible are therefore equal (`bv_poly_simp`); an equation between two
  unit multiples of differences gives the equivalence of the two equalities
  (`bv_poly_rel_eq`, the inverses of the units being supplied by the
  translator and checked by computation).

  Coefficients are unary naturals: the normal form of a width-n term costs
  arithmetic up to 2ⁿ·2ⁿ, which is fine for the widths of the regression
  benchmarks (8) and hopeless at 32.
*/
require open Stdlib.Bool Stdlib.Nat Stdlib.List Stdlib.PropExt Stdlib.Classic;
require open alethe.core;
require open alethe.prop;
require open Stdlib.Quotient;
require open alethe.bv;
require open Stdlib.Prod;
builtin "0" ≔ Stdlib.Nat._0;
builtin "1" ≔ Stdlib.Nat._1;
builtin "2" ≔ Stdlib.Nat._2;
builtin "3" ≔ Stdlib.Nat._3;
builtin "4" ≔ Stdlib.Nat._4;
builtin "5" ≔ Stdlib.Nat._5;
builtin "6" ≔ Stdlib.Nat._6;
builtin "7" ≔ Stdlib.Nat._7;
builtin "8" ≔ Stdlib.Nat._8;
builtin "9" ≔ Stdlib.Nat._9;
builtin "10" ≔ Stdlib.Nat._10;
builtin "+" ≔ Stdlib.Nat.+;
builtin "*" ≔ Stdlib.Nat.*;

/* ------------------------------------------------------------------------
   Group "ring": the ring laws of the bit-vector quotient.
   ------------------------------------------------------------------------ */

// The n low bits of c as a digit list (LSB first): `bvlit n (nat2bits n c)`
// is `class (≈ n) c`, so a numeral becomes a literal by computation.

opaque symbol bvadd_comm [n] (x y : τ (bitvec n)) : π (bvadd x y = bvadd y x) ≔
begin
  assume n; induction; assume a; induction; assume b;
  apply sound; simplify π;
  rewrite trunc_idem n (a + b); rewrite trunc_idem n (b + a);
  rewrite addnC a b; reflexivity
end;

opaque symbol bvadd_assoc [n] (x y z : τ (bitvec n)) : π (bvadd (bvadd x y) z = bvadd x (bvadd y z)) ≔
begin
  assume n; induction; assume a; induction; assume b; induction; assume c;
  apply sound; simplify π;
  rewrite trunc_idem n (trunc n (a + b) + c); rewrite trunc_idem n (a + trunc n (b + c));
  rewrite left (trunc_add_l n (a + b) c); rewrite left (trunc_add_r n a (b + c));
  reflexivity
end;

opaque symbol bvadd_zero_r [n] (x : τ (bitvec n)) : π (bvadd x (class (≈ n) 0) = x) ≔
begin
  assume n; induction; assume a;
  apply sound; simplify π;
  rewrite trunc_idem n (a + 0); reflexivity
end;

opaque symbol bvadd_zero_l [n] (x : τ (bitvec n)) : π (bvadd (class (≈ n) 0) x = x) ≔
begin
  assume n; induction; assume a;
  apply sound; simplify π;
  rewrite trunc_idem n (0 + a); reflexivity
end;

opaque symbol bvmul_comm [n] (x y : τ (bitvec n)) : π (bvmul x y = bvmul y x) ≔
begin
  assume n; induction; assume a; induction; assume b;
  apply sound; simplify π;
  rewrite trunc_idem n (a * b); rewrite trunc_idem n (b * a);
  rewrite mulnC a b; reflexivity
end;

opaque symbol bvmul_assoc [n] (x y z : τ (bitvec n)) : π (bvmul (bvmul x y) z = bvmul x (bvmul y z)) ≔
begin
  assume n; induction; assume a; induction; assume b; induction; assume c;
  apply sound; simplify π;
  rewrite trunc_idem n (trunc n (a * b) * c); rewrite trunc_idem n (a * trunc n (b * c));
  rewrite left (trunc_mul_l n (a * b) c); rewrite left (trunc_mul_r n a (b * c));
  rewrite mulnA a b c; reflexivity
end;

opaque symbol bvmul_one_l [n] (x : τ (bitvec n)) : π (bvmul (class (≈ n) 1) x = x) ≔
begin
  assume n; induction; assume a;
  apply sound; simplify π;
  rewrite trunc_idem n (1 * a); reflexivity
end;

opaque symbol bvmul_zero_l [n] (x : τ (bitvec n)) : π (bvmul (class (≈ n) 0) x = class (≈ n) 0) ≔
begin
  assume n; induction; assume a;
  apply sound; simplify π;
  rewrite trunc_idem n (0 * a); reflexivity
end;

opaque symbol bvmul_add_distr_l [n] (x y z : τ (bitvec n)) : π (bvmul x (bvadd y z) = bvadd (bvmul x y) (bvmul x z)) ≔
begin
  assume n; induction; assume a; induction; assume b; induction; assume c;
  apply sound; simplify π;
  rewrite trunc_idem n (a * trunc n (b + c)); rewrite trunc_idem n (trunc n (a * b) + trunc n (a * c));
  rewrite left (trunc_mul_r n a (b + c)); rewrite left (trunc_add_lr n (a * b) (a * c));
  rewrite mulnDr b c a; reflexivity
end;

opaque symbol bvmul_add_distr_r [n] (x y z : τ (bitvec n)) : π (bvmul (bvadd x y) z = bvadd (bvmul x z) (bvmul y z)) ≔
begin
  assume n; induction; assume a; induction; assume b; induction; assume c;
  apply sound; simplify π;
  rewrite trunc_idem n (trunc n (a + b) * c); rewrite trunc_idem n (trunc n (a * c) + trunc n (b * c));
  rewrite left (trunc_mul_l n (a + b) c); rewrite left (trunc_add_lr n (a * c) (b * c));
  rewrite mulnDl a b c; reflexivity
end;

opaque symbol bvadd_class n (a b : ℕ) : π (bvadd (class (≈ n) a) (class (≈ n) b) = class (≈ n) (trunc n (a + b))) ≔
begin
  assume n a b; reflexivity
end;

opaque symbol bvmul_class n (a b : ℕ) : π (bvmul (class (≈ n) a) (class (≈ n) b) = class (≈ n) (trunc n (a * b))) ≔
begin
  assume n a b; reflexivity
end;


opaque symbol bvmul_class_trunc [n] (a : ℕ) (x : τ (bitvec n)) : π (bvmul (class (≈ n) (trunc n a)) x = bvmul (class (≈ n) a) x) ≔
begin
  assume n a; induction; assume v;
  apply sound; simplify π;
  rewrite trunc_idem n (trunc n a * v); rewrite trunc_idem n (a * v);
  rewrite left (trunc_mul_l n a v); reflexivity
end;

opaque symbol bvmul_class_class [n] (a b : ℕ) (x : τ (bitvec n)) : π (bvmul (class (≈ n) a) (bvmul (class (≈ n) b) x) = bvmul (class (≈ n) (a * b)) x) ≔
begin
  assume n a b; induction; assume v;
  apply sound; simplify π;
  rewrite trunc_idem n (a * trunc n (b * v)); rewrite trunc_idem n (a * b * v);
  rewrite left (trunc_mul_r n a (b * v)); rewrite mulnA a b v; reflexivity
end;

opaque symbol bvsub_add_neg [n] (x y : τ (bitvec n)) : π (bvsub x y = bvadd x (bvneg y)) ≔
begin
  assume n; induction; assume a; induction; assume b;
  apply sound; simplify π;
  rewrite trunc_idem n (a + (2 ^ n - trunc n b));
  rewrite trunc_idem n (a + trunc n (2 ^ n - trunc n b));
  rewrite left (trunc_add_r n a (2 ^ n - trunc n b)); reflexivity
end;

// ---- helpers for bvneg_mul ----

// u * t + P = v + P * t when P = u +1 = v + t (no subtraction involved).
opaque symbol ring_neg_aux P u v t : π (u +1 = P) → π (v + t = P) → π (u * t + P = v + P * t) ≔
begin
  assume P u v t h1 h2;
  have h3 : π (u +1 = v + t) { rewrite h1; symmetry; refine h2 };
  rewrite left h1;
  change π (u * t + (u +1) = v + (t + u * t));
  rewrite h3;
  rewrite addnAC (u * t) v t;
  rewrite addnC (u * t) t;
  reflexivity
end;

// trunc_add_pow2 with q = 1, without the `2 ^ n * 1` spelling.
opaque symbol ring_trunc_add_pow2_1 n a : π (trunc n (a + 2 ^ n) = trunc n a) ≔
begin
  assume n a;
  refine ind_eq (eq_sym (muln1 (2 ^ n))) (λ z, trunc n (a + z) = trunc n a) (trunc_add_pow2 n a 1)
end;

// ---- requested lemmas ----

opaque symbol bvneg_mul [n] (x : τ (bitvec n)) : π (bvneg x = bvmul (class (≈ n) (2 ^ n - 1)) x) ≔
begin
  assume n; induction; assume a;
  apply sound; simplify π;
  rewrite trunc_idem n (2 ^ n - trunc n a); rewrite trunc_idem n ((2 ^ n - 1) * a);
  rewrite trunc_mul_r n (2 ^ n - 1) a;
  have e : π ((2 ^ n - 1) * trunc n a + 2 ^ n = (2 ^ n - trunc n a) + 2 ^ n * trunc n a)
  { refine ring_neg_aux (2 ^ n) (2 ^ n - 1) (2 ^ n - trunc n a) (trunc n a)
      (subnK 1 (2 ^ n) (pow2_gt0 n))
      (subnK (trunc n a) (2 ^ n) (ltnW (trunc n a) (2 ^ n) (trunc_lt n a))) };
  rewrite left (ring_trunc_add_pow2_1 n ((2 ^ n - 1) * trunc n a));
  rewrite e;
  rewrite trunc_add_pow2 n (2 ^ n - trunc n a) (trunc n a);
  reflexivity
end;

opaque symbol bvadd_neg_r [n] (x : τ (bitvec n)) : π (bvadd x (bvneg x) = class (≈ n) 0) ≔
begin
  assume n; induction; assume a;
  apply sound; simplify π;
  rewrite trunc_idem n (a + trunc n (2 ^ n - trunc n a));
  rewrite left (trunc_add_r n a (2 ^ n - trunc n a));
  rewrite trunc_add_l n a (2 ^ n - trunc n a);
  rewrite subnKC (trunc n a) (2 ^ n) (ltnW (trunc n a) (2 ^ n) (trunc_lt n a));
  refine ring_trunc_add_pow2_1 n 0
end;

// Purely algebraic: −(−x) = 0 + −(−x) = (x + −x) + −(−x) = x + (−x + −(−x)) = x + 0.
opaque symbol bvneg_neg [n] (x : τ (bitvec n)) : π (bvneg (bvneg x) = x) ≔
begin
  assume n x;
  rewrite left (bvadd_zero_l (bvneg (bvneg x)));
  rewrite left (bvadd_neg_r x);
  rewrite bvadd_assoc x (bvneg x) (bvneg (bvneg x));
  rewrite bvadd_neg_r (bvneg x);
  refine bvadd_zero_r x
end;

opaque symbol bvadd_cancel_l [n] (x y z : τ (bitvec n)) : π (bvadd x y = bvadd x z) → π (y = z) ≔
begin
  assume n x y z h;
  have e : Π w : τ (bitvec n), π (bvadd (bvneg x) (bvadd x w) = w)
  { assume w;
    rewrite left (bvadd_assoc (bvneg x) x w);
    rewrite bvadd_comm (bvneg x) x;
    rewrite bvadd_neg_r x;
    refine bvadd_zero_l w };
  refine eqt (eq_sym (e y)) (eqt (feq (bvadd (bvneg x)) h) (e z))
end;

opaque symbol bvsub_eq_zero [n] (x y : τ (bitvec n)) : π ((x = y) = (bvsub x y = class (≈ n) 0)) ≔
begin
  assume n x y;
  apply propExt
  { assume h; rewrite h; rewrite bvsub_add_neg y y; refine bvadd_neg_r y }
  { assume h;
    have h' : π (bvadd (bvneg y) x = bvadd (bvneg y) y)
    { rewrite bvadd_comm (bvneg y) x; rewrite bvadd_comm (bvneg y) y;
      rewrite left (bvsub_add_neg x y); rewrite h; symmetry; refine bvadd_neg_r y };
    refine bvadd_cancel_l (bvneg y) x y h' }
end;





/* ------------------------------------------------------------------------
   Two more ring facts (classes of sums and products, AC rearrangements).
   ------------------------------------------------------------------------ */

opaque symbol bvadd_class_add n (a b : ℕ) : π (bvadd (class (≈ n) a) (class (≈ n) b) = class (≈ n) (a + b)) ≔
begin
  assume n a b; rewrite bvadd_class n a b; refine class_trunc n (a + b)
end;

opaque symbol bvmul_class_mul n (a b : ℕ) : π (bvmul (class (≈ n) a) (class (≈ n) b) = class (≈ n) (a * b)) ≔
begin
  assume n a b; rewrite bvmul_class n a b; refine class_trunc n (a * b)
end;

opaque symbol bvadd_left_comm [n] (x y z : τ (bitvec n)) : π (bvadd x (bvadd y z) = bvadd y (bvadd x z)) ≔
begin
  assume n x y z;
  rewrite left (bvadd_assoc x y z); rewrite bvadd_comm x y; refine bvadd_assoc y x z
end;

opaque symbol bvadd_ACA [n] (a b c d : τ (bitvec n)) : π (bvadd (bvadd a b) (bvadd c d) = bvadd (bvadd a c) (bvadd b d)) ≔
begin
  assume n a b c d;
  rewrite bvadd_assoc a b (bvadd c d); rewrite bvadd_left_comm b c d;
  rewrite bvadd_assoc a c (bvadd b d); reflexivity
end;

/* ------------------------------------------------------------------------
   1. Syntax and denotation. Linear bit-vector expressions: a product of two
   non-literals is an atom (`BVar`), a product with a literal is `BMul`.
   ------------------------------------------------------------------------ */

inductive BExpr : TYPE ≔
| BCst : 𝕃 bool → BExpr
| BVar : ℕ → BExpr
| BAdd : BExpr → BExpr → BExpr
| BMul : 𝕃 bool → BExpr → BExpr
| BNeg : BExpr → BExpr
| BSub : BExpr → BExpr → BExpr;

constant symbol bexpr : Set;
rule τ bexpr ↪ BExpr;

symbol bdenote [n] : 𝕃 (bitvec n) → BExpr → τ (bitvec n);
rule @bdenote $n _ (BCst $l) ↪ bvlit $n $l
with @bdenote $n $env (BVar $i) ↪ nth (class (≈ $n) 0) $env $i
with @bdenote $n $env (BAdd $a $b) ↪ bvadd (@bdenote $n $env $a) (@bdenote $n $env $b)
with @bdenote $n $env (BMul $l $a) ↪ bvmul (bvlit $n $l) (@bdenote $n $env $a)
with @bdenote $n $env (BNeg $a) ↪ bvneg (@bdenote $n $env $a)
with @bdenote $n $env (BSub $a $b) ↪ bvsub (@bdenote $n $env $a) (@bdenote $n $env $b);

/* ------------------------------------------------------------------------
   2. Reification by rewriting (the lia.lp/lra.lp discipline). `bfind` is
   sequential: it returns the index of a term that is convertible to an
   element of the environment, or `BNew k` with k the next free index. `brfy`
   is sequential too: its last rule makes any other term an atom. Neither may
   be reduced on a bound variable inside a proof; they are only ever run on
   the concrete terms of a step, and `bv_poly_simp` takes the resulting
   equations as hypotheses closed by `eq_refl`.
   ------------------------------------------------------------------------ */

constant symbol BR : TYPE;
constant symbol BIndex : ℕ → BR;
constant symbol BNew : ℕ → BR;

symbol bcase [a] : BR → (ℕ → τ a) → (ℕ → τ a) → τ a;
rule bcase (BIndex $i) $f _ ↪ $f $i
with bcase (BNew $i) _ $g ↪ $g $i;

sequential symbol bfind : ℕ → Π [a], τ a → 𝕃 a → BR;
rule bfind $k _ □ ↪ BNew $k
with bfind $k $x ($x ⸬ _) ↪ BIndex $k
with bfind $k $x (_ ⸬ $l) ↪ bfind ($k +1) $x $l;

sequential symbol brfy [n] : 𝕃 (bitvec n) → τ (bitvec n) → τ (bexpr × list (bitvec n));
rule @brfy $n $l (@bvadd _ $x $y) ↪
  let x ≔ @brfy $n $l $x in let y ≔ @brfy $n (x ₂) $y in BAdd (x ₁) (y ₁) ‚ (y ₂)
with @brfy $n $l (@bvsub _ $x $y) ↪
  let x ≔ @brfy $n $l $x in let y ≔ @brfy $n (x ₂) $y in BSub (x ₁) (y ₁) ‚ (y ₂)
with @brfy $n $l (@bvneg _ $x) ↪
  let x ≔ @brfy $n $l $x in BNeg (x ₁) ‚ (x ₂)
with @brfy $n $l (@bvmul _ (bvlit _ $c) $y) ↪
  let y ≔ @brfy $n $l $y in BMul $c (y ₁) ‚ (y ₂)
with @brfy $n $l (@bvmul _ $x (bvlit _ $c)) ↪
  let x ≔ @brfy $n $l $x in BMul $c (x ₁) ‚ (x ₂)
with @brfy _ $l (bvlit _ $c) ↪ BCst $c ‚ $l
// any other term is an atom
with @brfy _ $l $x ↪
  bcase (bfind 0 $x $l) (λ i, BVar i ‚ $l) (λ i, BVar i ‚ ($l ++ ($x ⸬ □)));

// Denotation after reification is the term again, by conversion.
assert (x y : τ (bitvec 8)) (l : 𝕃 bool) ⊢
  brfy □ (bvadd x (bvmul (bvlit 8 l) y)) ≡ (BAdd (BVar 0) (BMul l (BVar 1)) ‚ (x ⸬ y ⸬ □));
assert (x y : τ (bitvec 8)) (l : 𝕃 bool) ⊢
  bdenote (brfy □ (bvadd x (bvmul (bvlit 8 l) y)) ₂) (brfy □ (bvadd x (bvmul (bvlit 8 l) y)) ₁)
  ≡ bvadd x (bvmul (bvlit 8 l) y);
// repeated atoms share an index; a product of two atoms is itself an atom
assert (x y : τ (bitvec 8)) ⊢
  brfy □ (bvsub (bvmul x y) (bvadd x (bvmul x y))) ≡ (BSub (BVar 0) (BAdd (BVar 1) (BVar 0)) ‚ (bvmul x y ⸬ x ⸬ □));

/* ------------------------------------------------------------------------
   3. Normal form: a sorted list of monomials (coefficient, atom index) and a
   constant, everything reduced modulo 2ⁿ, zero coefficients dropped.
   ------------------------------------------------------------------------ */

// `c ·xᵢ` prepended unless c = 0
symbol bcons_nz : ℕ → ℕ → 𝕃 (nat × nat) → 𝕃 (nat × nat);
rule bcons_nz 0 _ $ms ↪ $ms
with bcons_nz ($c +1) $i $ms ↪ (($c +1) ‚ $i) ⸬ $ms;

// every coefficient scaled by k, modulo 2ⁿ
symbol bscale : ℕ → ℕ → 𝕃 (nat × nat) → 𝕃 (nat × nat);
rule bscale _ _ □ ↪ □
with bscale $n $k (($c ‚ $i) ⸬ $ms) ↪ bcons_nz (trunc $n ($k * $c)) $i (bscale $n $k $ms);

// merge of two lists sorted by index, equal indices added modulo 2ⁿ
symbol bmerge : ℕ → 𝕃 (nat × nat) → 𝕃 (nat × nat) → 𝕃 (nat × nat);
rule bmerge _ □ $q ↪ $q
with bmerge _ ($m ⸬ $p) □ ↪ $m ⸬ $p
with bmerge $n (($c ‚ $i) ⸬ $p) (($d ‚ $j) ⸬ $q) ↪
  if (eqn $i $j) (bcons_nz (trunc $n ($c + $d)) $i (bmerge $n $p $q))
    (if ($i < $j) (($c ‚ $i) ⸬ bmerge $n $p (($d ‚ $j) ⸬ $q))
                  (($d ‚ $j) ⸬ bmerge $n (($c ‚ $i) ⸬ $p) $q));

// sum and scalar multiple of two linear forms (monomials ‚ constant)
symbol badd : ℕ → τ (list (nat × nat) × nat) → τ (list (nat × nat) × nat) → τ (list (nat × nat) × nat);
rule badd $n ($p ‚ $c) ($q ‚ $d) ↪ bmerge $n $p $q ‚ trunc $n ($c + $d);

symbol bmul : ℕ → ℕ → τ (list (nat × nat) × nat) → τ (list (nat × nat) × nat);
rule bmul $n $k ($p ‚ $c) ↪ bscale $n $k $p ‚ trunc $n ($k * $c);

// the linear form of an expression at width n (negation is scaling by 2ⁿ − 1)
symbol blin : ℕ → BExpr → τ (list (nat × nat) × nat);
rule blin $n (BCst $l) ↪ □ ‚ trunc $n (bits2natB $l)
with blin _ (BVar $i) ↪ ((1 ‚ $i) ⸬ □) ‚ 0
with blin $n (BAdd $a $b) ↪ badd $n (blin $n $a) (blin $n $b)
with blin $n (BMul $l $a) ↪ bmul $n (bits2natB $l) (blin $n $a)
with blin $n (BNeg $a) ↪ bmul $n (2 ^ $n - 1) (blin $n $a)
with blin $n (BSub $a $b) ↪ blin $n (BAdd $a (BNeg $b));

assert ⊢ blin 4 (BAdd (BVar 1) (BAdd (BCst (true ⸬ □)) (BMul (true ⸬ true ⸬ □) (BVar 0))))
       ≡ ((3 ‚ 0) ⸬ (1 ‚ 1) ⸬ □) ‚ 1;
assert ⊢ blin 4 (BSub (BVar 0) (BVar 0)) ≡ □ ‚ 0;
assert ⊢ blin 4 (BNeg (BCst (true ⸬ □))) ≡ □ ‚ 15;
assertnot ⊢ blin 4 (BVar 0) ≡ blin 4 (BVar 1);

// The value of a linear form, with the coefficients as literals.
symbol bval [n] : 𝕃 (bitvec n) → τ (list (nat × nat) × nat) → τ (bitvec n);
rule @bval $n _ (□ ‚ $c) ↪ bvlit $n (nat2bits $n $c)
with @bval $n $env ((($k ‚ $i) ⸬ $ms) ‚ $c) ↪
  bvadd (bvmul (bvlit $n (nat2bits $n $k)) (nth (class (≈ $n) 0) $env $i)) (@bval $n $env ($ms ‚ $c));

// The same with the coefficients as classes and no constant: the proofs
// below live here, `bval_eq` relates the two.
symbol bvalm [n] : 𝕃 (bitvec n) → 𝕃 (nat × nat) → τ (bitvec n);
rule @bvalm $n _ □ ↪ class (≈ $n) 0
with @bvalm $n $env (($k ‚ $i) ⸬ $ms) ↪
  bvadd (bvmul (class (≈ $n) $k) (nth (class (≈ $n) 0) $env $i)) (@bvalm $n $env $ms);

opaque symbol bval_const [n] (env : 𝕃 (bitvec n)) (c : ℕ) : π (bval env (□ ‚ c) = class (≈ n) c) ≔
begin
  assume n env c; refine bvlit_nat2bits n c
end;

opaque symbol bval_eq [n] (env : 𝕃 (bitvec n)) (ms : 𝕃 (nat × nat)) (c : ℕ) :
  π (bval env (ms ‚ c) = bvadd (bvalm env ms) (class (≈ n) c)) ≔
begin
  assume n env; induction
  { assume c;
    change π (bvlit n (nat2bits n c) = bvadd (class (≈ n) 0) (class (≈ n) c));
    rewrite bvlit_nat2bits n c; rewrite bvadd_zero_l (class (≈ n) c); reflexivity }
  { induction; assume k i ms ih c;
    change π (bvadd (bvmul (bvlit n (nat2bits n k)) (nth (class (≈ n) 0) env i)) (bval env (ms ‚ c))
              = bvadd (bvadd (bvmul (class (≈ n) k) (nth (class (≈ n) 0) env i)) (bvalm env ms)) (class (≈ n) c));
    rewrite ih c; rewrite bvlit_nat2bits n k;
    rewrite bvadd_assoc (bvmul (class (≈ n) k) (nth (class (≈ n) 0) env i)) (bvalm env ms) (class (≈ n) c);
    reflexivity }
end;

opaque symbol bvalm_cons_nz [n] (env : 𝕃 (bitvec n)) (c i : ℕ) (ms : 𝕃 (nat × nat)) :
  π (bvalm env (bcons_nz c i ms) = bvadd (bvmul (class (≈ n) c) (nth (class (≈ n) 0) env i)) (bvalm env ms)) ≔
begin
  assume n env; induction
  { assume i ms;
    change π (bvalm env ms = bvadd (bvmul (class (≈ n) 0) (nth (class (≈ n) 0) env i)) (bvalm env ms));
    rewrite bvmul_zero_l (nth (class (≈ n) 0) env i); rewrite bvadd_zero_l (bvalm env ms); reflexivity }
  { assume c ih i ms; reflexivity }
end;

opaque symbol bval_scale [n] (env : 𝕃 (bitvec n)) (k : ℕ) (p : 𝕃 (nat × nat)) :
  π (bvalm env (bscale n k p) = bvmul (class (≈ n) k) (bvalm env p)) ≔
begin
  assume n env k; induction
  { change π (class (≈ n) 0 = bvmul (class (≈ n) k) (class (≈ n) 0));
    rewrite bvmul_comm (class (≈ n) k) (class (≈ n) 0); rewrite bvmul_zero_l (class (≈ n) k); reflexivity }
  { induction; assume c i p ih;
    change π (bvalm env (bcons_nz (trunc n (k * c)) i (bscale n k p))
              = bvmul (class (≈ n) k) (bvadd (bvmul (class (≈ n) c) (nth (class (≈ n) 0) env i)) (bvalm env p)));
    rewrite bvalm_cons_nz env (trunc n (k * c)) i (bscale n k p);
    rewrite ih;
    rewrite bvmul_class_trunc (k * c) (nth (class (≈ n) 0) env i);
    rewrite left (bvmul_class_class k c (nth (class (≈ n) 0) env i));
    symmetry;
    refine bvmul_add_distr_l (class (≈ n) k) (bvmul (class (≈ n) c) (nth (class (≈ n) 0) env i)) (bvalm env p) }
end;

opaque symbol bval_merge [n] (env : 𝕃 (bitvec n)) (p q : 𝕃 (nat × nat)) :
  π (bvalm env (bmerge n p q) = bvadd (bvalm env p) (bvalm env q)) ≔
begin
  assume n env; induction
  { assume q;
    change π (bvalm env q = bvadd (class (≈ n) 0) (bvalm env q));
    rewrite bvadd_zero_l (bvalm env q); reflexivity }
  { induction; assume c i p ihp; induction
    { change π (bvalm env ((c ‚ i) ⸬ p) = bvadd (bvalm env ((c ‚ i) ⸬ p)) (class (≈ n) 0));
      rewrite bvadd_zero_r (bvalm env ((c ‚ i) ⸬ p)); reflexivity }
    { induction; assume d j q ihq;
      change π (bvalm env (if (eqn i j) (bcons_nz (trunc n (c + d)) i (bmerge n p q))
                             (if (i < j) ((c ‚ i) ⸬ bmerge n p ((d ‚ j) ⸬ q))
                                         ((d ‚ j) ⸬ bmerge n ((c ‚ i) ⸬ p) q)))
                = bvadd (bvalm env ((c ‚ i) ⸬ p)) (bvalm env ((d ‚ j) ⸬ q)));
      apply ∨ₑ (case_𝔹 (eqn i j))
      { assume he; rewrite he;
        have hij : π (i = j) { refine eqn_correct i j (true=istrue he) };
        rewrite hij;
        change π (bvalm env (bcons_nz (trunc n (c + d)) j (bmerge n p q))
                  = bvadd (bvadd (bvmul (class (≈ n) c) (nth (class (≈ n) 0) env j)) (bvalm env p))
                          (bvadd (bvmul (class (≈ n) d) (nth (class (≈ n) 0) env j)) (bvalm env q)));
        rewrite bvalm_cons_nz env (trunc n (c + d)) j (bmerge n p q);
        rewrite ihp q;
        rewrite bvmul_class_trunc (c + d) (nth (class (≈ n) 0) env j);
        rewrite left (bvadd_class_add n c d);
        rewrite bvmul_add_distr_r (class (≈ n) c) (class (≈ n) d) (nth (class (≈ n) 0) env j);
        refine bvadd_ACA (bvmul (class (≈ n) c) (nth (class (≈ n) 0) env j))
                         (bvmul (class (≈ n) d) (nth (class (≈ n) 0) env j)) (bvalm env p) (bvalm env q) }
      { assume he; rewrite he;
        apply ∨ₑ (case_𝔹 (i < j))
        { assume hlt; rewrite hlt;
          change π (bvadd (bvmul (class (≈ n) c) (nth (class (≈ n) 0) env i)) (bvalm env (bmerge n p ((d ‚ j) ⸬ q)))
                    = bvadd (bvadd (bvmul (class (≈ n) c) (nth (class (≈ n) 0) env i)) (bvalm env p)) (bvalm env ((d ‚ j) ⸬ q)));
          rewrite ihp ((d ‚ j) ⸬ q);
          symmetry;
          refine bvadd_assoc (bvmul (class (≈ n) c) (nth (class (≈ n) 0) env i)) (bvalm env p) (bvalm env ((d ‚ j) ⸬ q)) }
        { assume hge; rewrite hge;
          change π (bvadd (bvmul (class (≈ n) d) (nth (class (≈ n) 0) env j)) (bvalm env (bmerge n ((c ‚ i) ⸬ p) q))
                    = bvadd (bvalm env ((c ‚ i) ⸬ p)) (bvadd (bvmul (class (≈ n) d) (nth (class (≈ n) 0) env j)) (bvalm env q)));
          rewrite ihq;
          refine bvadd_left_comm (bvmul (class (≈ n) d) (nth (class (≈ n) 0) env j)) (bvalm env ((c ‚ i) ⸬ p)) (bvalm env q) } } } }
end;

opaque symbol badd_correct [n] (env : 𝕃 (bitvec n)) (P Q : τ (list (nat × nat) × nat)) :
  π (bval env (badd n P Q) = bvadd (bval env P) (bval env Q)) ≔
begin
  assume n env; induction; assume p c; induction; assume q d;
  change π (bval env (bmerge n p q ‚ trunc n (c + d)) = bvadd (bval env (p ‚ c)) (bval env (q ‚ d)));
  rewrite bval_eq env (bmerge n p q) (trunc n (c + d));
  rewrite bval_eq env p c; rewrite bval_eq env q d;
  rewrite bval_merge env p q;
  rewrite class_trunc n (c + d);
  rewrite left (bvadd_class_add n c d);
  refine bvadd_ACA (bvalm env p) (bvalm env q) (class (≈ n) c) (class (≈ n) d)
end;

opaque symbol bmul_correct [n] (env : 𝕃 (bitvec n)) (k : ℕ) (P : τ (list (nat × nat) × nat)) :
  π (bval env (bmul n k P) = bvmul (class (≈ n) k) (bval env P)) ≔
begin
  assume n env k; induction; assume p c;
  change π (bval env (bscale n k p ‚ trunc n (k * c)) = bvmul (class (≈ n) k) (bval env (p ‚ c)));
  rewrite bval_eq env (bscale n k p) (trunc n (k * c));
  rewrite bval_eq env p c;
  rewrite bval_scale env k p;
  rewrite class_trunc n (k * c);
  rewrite left (bvmul_class_mul n k c);
  symmetry; refine bvmul_add_distr_l (class (≈ n) k) (bvalm env p) (class (≈ n) c)
end;

opaque symbol blin_correct [n] (env : 𝕃 (bitvec n)) (e : BExpr) : π (bval env (blin n e) = bdenote env e) ≔
begin
  assume n env; induction
  // BCst
  { assume l;
    change π (bval env (□ ‚ trunc n (bits2natB l)) = bvlit n l);
    rewrite bval_const env (trunc n (bits2natB l)); rewrite class_trunc n (bits2natB l);
    rewrite bvlit_class n l; reflexivity }
  // BVar
  { assume i;
    change π (bvadd (bvmul (bvlit n (nat2bits n 1)) (nth (class (≈ n) 0) env i)) (bvlit n (nat2bits n 0))
              = nth (class (≈ n) 0) env i);
    rewrite bvlit_nat2bits n 1; rewrite bvlit_nat2bits n 0;
    rewrite bvmul_one_l (nth (class (≈ n) 0) env i); rewrite bvadd_zero_r (nth (class (≈ n) 0) env i);
    reflexivity }
  // BAdd
  { assume a iha b ihb;
    change π (bval env (badd n (blin n a) (blin n b)) = bvadd (bdenote env a) (bdenote env b));
    rewrite badd_correct env (blin n a) (blin n b); rewrite iha; rewrite ihb; reflexivity }
  // BMul
  { assume l a iha;
    change π (bval env (bmul n (bits2natB l) (blin n a)) = bvmul (bvlit n l) (bdenote env a));
    rewrite bmul_correct env (bits2natB l) (blin n a); rewrite iha; rewrite bvlit_class n l; reflexivity }
  // BNeg
  { assume a iha;
    change π (bval env (bmul n (2 ^ n - 1) (blin n a)) = bvneg (bdenote env a));
    rewrite bmul_correct env (2 ^ n - 1) (blin n a); rewrite iha; rewrite bvneg_mul (bdenote env a); reflexivity }
  // BSub
  { assume a iha b ihb;
    change π (bval env (badd n (blin n a) (bmul n (2 ^ n - 1) (blin n b))) = bvsub (bdenote env a) (bdenote env b));
    rewrite badd_correct env (blin n a) (bmul n (2 ^ n - 1) (blin n b));
    rewrite bmul_correct env (2 ^ n - 1) (blin n b); rewrite iha; rewrite ihb;
    rewrite bvsub_add_neg (bdenote env a) (bdenote env b); rewrite bvneg_mul (bdenote env b); reflexivity }
end;

/* ------------------------------------------------------------------------
   4. The two end-user lemmas.
   ------------------------------------------------------------------------ */

// poly_simp: `set r ≔ brfy □ a; set s ≔ brfy (r ₂) b;
//             refine bv_poly_simp (s ₂) (r ₁) (s ₁) a b (eq_refl _) (eq_refl _) (eq_refl _)`
opaque symbol bv_poly_simp [n] (env : 𝕃 (bitvec n)) (ea eb : BExpr) (a b : τ (bitvec n)) :
  π (bdenote env ea = a) → π (bdenote env eb = b) → π (blin n ea = blin n eb) → π (a = b) ≔
begin
  assume n env ea eb a b ha hb h;
  rewrite left ha; rewrite left hb;
  rewrite left (blin_correct env ea); rewrite left (blin_correct env eb);
  rewrite h; reflexivity
end;

// A literal that is a unit modulo 2ⁿ (d·c ≡ 1) can be cancelled against 0.
opaque symbol unit_cancel [n] (lc ld : 𝕃 bool) (x : τ (bitvec n)) :
  π (istrue (eqn (trunc n (bits2natB ld * bits2natB lc)) 1)) →
  π ((bvmul (bvlit n lc) x = class (≈ n) 0) = (x = class (≈ n) 0)) ≔
begin
  assume n lc ld x h;
  have h1 : π (trunc n (bits2natB ld * bits2natB lc) = 1)
  { refine eqn_correct (trunc n (bits2natB ld * bits2natB lc)) 1 h };
  have e : π (x = bvmul (class (≈ n) (bits2natB ld)) (bvmul (bvlit n lc) x))
  { rewrite bvlit_class n lc;
    rewrite bvmul_class_class (bits2natB ld) (bits2natB lc) x;
    rewrite left (bvmul_class_trunc (bits2natB ld * bits2natB lc) x);
    rewrite h1; symmetry; refine bvmul_one_l x };
  apply propExt
  { assume hx; rewrite e; rewrite hx;
    rewrite bvmul_comm (class (≈ n) (bits2natB ld)) (class (≈ n) 0);
    refine bvmul_zero_l (class (≈ n) (bits2natB ld)) }
  { assume hx; rewrite hx;
    rewrite bvmul_comm (bvlit n lc) (class (≈ n) 0);
    refine bvmul_zero_l (bvlit n lc) }
end;

// poly_simp_rel: `refine bv_poly_rel_eq lc1 ld1 lc2 ld2 s t u v ⊤ᵢ ⊤ᵢ (π̇ₗ premise)`
// with lcᵢ the digits of the coefficient cᵢ and ldᵢ those of its inverse modulo 2ⁿ.
opaque symbol bv_poly_rel_eq [n] (lc1 ld1 lc2 ld2 : 𝕃 bool) (s t u v : τ (bitvec n)) :
  π (istrue (eqn (trunc n (bits2natB ld1 * bits2natB lc1)) 1)) →
  π (istrue (eqn (trunc n (bits2natB ld2 * bits2natB lc2)) 1)) →
  π (bvmul (bvlit n lc1) (bvsub s t) = bvmul (bvlit n lc2) (bvsub u v)) →
  π ((s = t) = (u = v)) ≔
begin
  assume n lc1 ld1 lc2 ld2 s t u v h1 h2 h;
  rewrite bvsub_eq_zero s t; rewrite bvsub_eq_zero u v;
  rewrite left (unit_cancel lc1 ld1 (bvsub s t) h1);
  rewrite left (unit_cancel lc2 ld2 (bvsub u v) h2);
  rewrite h; reflexivity
end;

/* ------------------------------------------------------------------------
   Tests (cvc5's qbv-test-invert-bvadd-neq, steps t66 and t72.t3.t0, width 8).
   ------------------------------------------------------------------------ */

assert (x y : τ (bitvec 8)) (l : 𝕃 bool) ⊢
  bdenote (brfy □ (bvadd x (bvmul (bvlit 8 l) y)) ₂) (brfy □ (bvadd x (bvmul (bvlit 8 l) y)) ₁)
  ≡ bvadd x (bvmul (bvlit 8 l) y);

// t66: #xff + (−a) + b = b + (−a) + #xff
opaque symbol bvpoly_test_t66 (a b : τ (bitvec 8)) :
  π (bvadd (bvadd (bvlit 8 (true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ □)) (bvneg a)) b
     = bvadd (bvadd b (bvneg a)) (bvlit 8 (true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ □))) ≔
begin
  assume a b;
  refine (bv_poly_simp
    (brfy (brfy □ (bvadd (bvadd (bvlit 8 (true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ □)) (bvneg a)) b) ₂)
          (bvadd (bvadd b (bvneg a)) (bvlit 8 (true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ □))) ₂)
    (brfy □ (bvadd (bvadd (bvlit 8 (true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ □)) (bvneg a)) b) ₁)
    (brfy (brfy □ (bvadd (bvadd (bvlit 8 (true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ □)) (bvneg a)) b) ₂)
          (bvadd (bvadd b (bvneg a)) (bvlit 8 (true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ □))) ₁)
    (bvadd (bvadd (bvlit 8 (true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ □)) (bvneg a)) b)
    (bvadd (bvadd b (bvneg a)) (bvlit 8 (true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ □)))
    (eq_refl _) (eq_refl _) (eq_refl _))
end;

// t72.t3.t0: #xff · ((x + a) − b) = #x01 · (b − (x + a)), in the translator's own script shape
opaque symbol bvpoly_test_t72 (x a b : τ (bitvec 8)) :
  π (bvmul (bvlit 8 (true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ □)) (bvsub (bvadd x a) b)
     = bvmul (bvlit 8 (true ⸬ false ⸬ false ⸬ false ⸬ false ⸬ false ⸬ false ⸬ false ⸬ □)) (bvsub b (bvadd x a))) ≔
begin
  assume x a b;
  set r ≔ (brfy □ (bvmul (bvlit 8 (true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ □)) (bvsub (bvadd x a) b)));
  set s ≔ (brfy (r ₂) (bvmul (bvlit 8 (true ⸬ false ⸬ false ⸬ false ⸬ false ⸬ false ⸬ false ⸬ false ⸬ □)) (bvsub b (bvadd x a))));
  refine (bv_poly_simp (s ₂) (r ₁) (s ₁)
    (bvmul (bvlit 8 (true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ true ⸬ □)) (bvsub (bvadd x a) b))
    (bvmul (bvlit 8 (true ⸬ false ⸬ false ⸬ false ⸬ false ⸬ false ⸬ false ⸬ false ⸬ □)) (bvsub b (bvadd x a)))
    (eq_refl _) (eq_refl _) (eq_refl _))
end;

// poly_simp_rel at width 4: 15⁻¹ = 15 and 1⁻¹ = 1 modulo 16.
opaque symbol bvpoly_test_rel (a b : τ (bitvec 4)) :
  π (bvmul (bvlit 4 (true ⸬ true ⸬ true ⸬ true ⸬ □)) (bvsub a b) = bvmul (bvlit 4 (true ⸬ false ⸬ false ⸬ false ⸬ □)) (bvsub b a)) →
  π ((a = b) = (b = a)) ≔
begin
  assume a b h;
  refine (bv_poly_rel_eq (true ⸬ true ⸬ true ⸬ true ⸬ □) (true ⸬ true ⸬ true ⸬ true ⸬ □)
                         (true ⸬ false ⸬ false ⸬ false ⸬ □) (true ⸬ false ⸬ false ⸬ false ⸬ □) a b b a ⊤ᵢ ⊤ᵢ h)
end;
