/*
  SMT-LIB fixed-size bit-vectors as a quotient of ℕ (Stdlib.Quotient).

    BitVec n  :=  ℕ ⫽ (≈ n)        a ≈ₙ b  iff  trunc n a = trunc n b

  where `trunc n x` is the low n bits of x, i.e. x mod 2ⁿ. Signed and
  unsigned operations share the same classes; signedness only changes the
  reading of a class (see `flip`, `bvslt`).

  Three views of a bit-vector live here, and every operation relates them:
  - `cl v`      a representative v : ℕ (unary). Rules on `cl` are the
                mathematics: `bvadd (cl x) (cl y) ↪ class (≈ n) (trunc n (x + y))`.
                Each such rule is certified by a hypothesis-free `*_compat`
                lemma (its right-hand side only reads `trunc n x`), which is
                exactly what makes it sound under the quotient's `sound`.
  - `bvlit n l` a literal, as an LSB-first Boolean digit list. ℕ is unary, so
                a 32-bit constant can never be normalised; `bvlit` is made
                opaque once its defining equation `bvlit_def` is proved, and
                closed computation on literals is done by rules on digit lists
                that are proved as equations before being installed.
  - `bbterm n L` cvc5's bit-blasted term, a list of n propositions (LSB first),
                defined as `bvlit n (map pb L)` with `pb : Prop → 𝔹`.
*/
require open Stdlib.Bool Stdlib.Nat Stdlib.List Stdlib.PropExt Stdlib.Classic;
require open alethe.core;        // Bool ≔ o, prop_ext, …; core's `cl : Set` and tactic `and` shadow from here
require open alethe.prop;        // `xor` on propositions, the one the translator prints
require open Stdlib.Quotient;    // `cl` is the quotient constructor again
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
   Truncation: the low n bits of x, i.e. x mod 2ⁿ. Recursion on n mirrors
   Stdlib.Nat.bitwise, so closed representatives compute and the bit-level
   lemmas are one-line inductions.
   ------------------------------------------------------------------------ */

symbol bit (x : ℕ) : ℕ ≔ if (odd x) 1 0;

symbol trunc : ℕ → ℕ → ℕ;
rule trunc 0 _ ↪ 0
with trunc ($n +1) $x ↪ bit $x + 2 * trunc $n (div2 $x);

assert ⊢ trunc 8 300 ≡ 44;
assert ⊢ trunc 3 7 ≡ 7;
assert ⊢ trunc 0 5 ≡ 0;

/* ------------------------------------------------------------------------
   The relation and the quotient.

   `≈` is a constant whose meaning is a rule on `π`: an applied `≈ n a b`
   stays a rigid head, so `Quot (≈ ?n) ≡ Quot (≈ 8)` solves the width by
   decomposition, while `π (≈ n a b)` converts to the equation of truncations.
   Tactics that match syntactically (`rewrite`) see the equation after
   `simplify π`; `refine`, `apply` and `reflexivity` see it by conversion.
   ------------------------------------------------------------------------ */

constant symbol ≈ : ℕ → ℕ → ℕ → Prop;
rule π (≈ $n $a $b) ↪ π (trunc $n $a = trunc $n $b);

opaque symbol ≈_refl n x : π (≈ n x x) ≔
begin
  assume n x; reflexivity
end;

opaque symbol ≈_sym n x y : π (≈ n x y) → π (≈ n y x) ≔
begin
  assume n x y h; symmetry; refine h
end;

opaque symbol ≈_trans n x y z : π (≈ n x y) → π (≈ n y z) → π (≈ n x z) ≔
begin
  assume n x y z hxy hyz; simplify π; rewrite hxy; refine hyz
end;

// A definition (not a constant with its own τ-rule): then `τ ?s ≡ Quot (≈ n)`
// has a unique inverse through Stdlib.Quotient's rule, which is what lets a
// bare `=` between bit-vectors infer its sort.
symbol bitvec (n : ℕ) : Set ≔ nat ⫽ (≈ n);

// `trunc n` respects `≈ n` by definition. (A named lemma rather than a λ: with
// metavariables around, unification decomposes the injective `π` instead of
// converting `π (≈ n x y)`.)
opaque symbol trunc_compat n x y : π (≈ n x y) → π (trunc n x = trunc n y) ≔
begin
  assume n x y h; refine h
end;

// The canonical representative, through `lift`: compatibility is enforced by
// typing, and `repr (cl v)` reduces to `trunc n v`.
symbol repr [n] : τ (bitvec n) → ℕ ≔ lift (≈ n) (trunc n) (trunc_compat n);

assert n v ⊢ repr (class (≈ n) v) ≡ trunc n v;

/* ------------------------------------------------------------------------
   Bits as propositions, literals as digit lists.
   ------------------------------------------------------------------------ */

// `pb` reads a proposition as a bit. With `em` and `prop_ext`, Prop is
// two-valued (`prop_2val` below), so a function Prop → 𝔹 is determined by its
// values at ⊤ and ⊥: these two rules are its definition.
symbol pb : Prop → 𝔹;
rule pb ⊤ ↪ true
with pb ⊥ ↪ false;

// Boolean equality on digits (decides literal equality cellwise).
symbol eqb (a b : 𝔹) : 𝔹 ≔ Stdlib.Bool.not (a xorb b);

// The value of a digit list, least significant digit first.
symbol bits2natB : 𝕃 bool → ℕ;
rule bits2natB □ ↪ 0
with bits2natB ($b ⸬ $l) ↪ (if $b 1 0) + 2 * bits2natB $l;

// Exactly n digits.
symbol fit (n : ℕ) (l : 𝕃 bool) : 𝕃 bool ≔ take n (l ++ nseq n false);

// A literal. #b0011 is `bvlit 4 (true ⸬ true ⸬ false ⸬ false ⸬ □)`.
symbol bvlit (n : ℕ) (l : 𝕃 bool) : τ (bitvec n) ≔ class (≈ n) (bits2natB l);

opaque symbol bvlit_def n l : π (bvlit n l = class (≈ n) (bits2natB l)) ≔
begin
  assume n l; reflexivity
end;

// cvc5's `@bbterm b₀ … bₙ₋₁`: a bit-vector given by n propositions, LSB first.
symbol bbterm (n : ℕ) (L : 𝕃 o) : τ (bitvec n) ≔ bvlit n (map pb L);

opaque symbol bbterm_def n L : π (bbterm n L = bvlit n (map pb L)) ≔
begin
  assume n L; reflexivity
end;

// cvc5's `(_ @bit_of i) x`. The rule on `cl` reads `trunc n x` only, hence
// respects `≈ n`; the rule on literals is installed below, once proved.
symbol bit_of [n] (i : ℕ) : τ (bitvec n) → Prop;
rule @bit_of $n $i (cl $x) ↪ istrue (testbit (trunc $n $x) $i);

/* ------------------------------------------------------------------------
   Operations: rules on `cl`. The right-hand side is always a class of a
   function of `trunc n x` (and `trunc n y`), so closed representatives are
   canonical and the compatibility certificates below have no hypotheses.
   ------------------------------------------------------------------------ */

symbol bvadd [n] : τ (bitvec n) → τ (bitvec n) → τ (bitvec n);
rule @bvadd $n (cl $x) (cl $y) ↪ class (≈ $n) (trunc $n ($x + $y));

symbol bvmul [n] : τ (bitvec n) → τ (bitvec n) → τ (bitvec n);
rule @bvmul $n (cl $x) (cl $y) ↪ class (≈ $n) (trunc $n ($x * $y));

symbol bvneg [n] : τ (bitvec n) → τ (bitvec n);
rule @bvneg $n (cl $x) ↪ class (≈ $n) (trunc $n (2 ^ $n - trunc $n $x));

symbol bvsub [n] : τ (bitvec n) → τ (bitvec n) → τ (bitvec n);
rule @bvsub $n (cl $x) (cl $y) ↪ class (≈ $n) (trunc $n ($x + (2 ^ $n - trunc $n $y)));

// Bitwise operations through Stdlib.Nat.bitwise with the width as fuel: it
// only ever reads the low n bits of its arguments and produces at most n bits.
symbol bvand [n] : τ (bitvec n) → τ (bitvec n) → τ (bitvec n);
rule @bvand $n (cl $x) (cl $y) ↪ class (≈ $n) (bitwise (Stdlib.Bool.and) $n $x $y);

symbol bvor [n] : τ (bitvec n) → τ (bitvec n) → τ (bitvec n);
rule @bvor $n (cl $x) (cl $y) ↪ class (≈ $n) (bitwise (Stdlib.Bool.or) $n $x $y);

symbol bvxor [n] : τ (bitvec n) → τ (bitvec n) → τ (bitvec n);
rule @bvxor $n (cl $x) (cl $y) ↪ class (≈ $n) (bitwise (Stdlib.Bool.xorb) $n $x $y);

symbol bvnot [n] : τ (bitvec n) → τ (bitvec n);
rule @bvnot $n (cl $x) ↪ class (≈ $n) (bitwise (λ (a _ : 𝔹), Stdlib.Bool.not a) $n $x $x);

// `concat x y`: x is the high part, y the low part.
symbol concat [m n] : τ (bitvec m) → τ (bitvec n) → τ (bitvec (m + n));
rule @concat $m $n (cl $x) (cl $y) ↪ class (≈ ($m + $n)) (trunc $n $y + (trunc $m $x <<< $n));

// `extract i j x`: bits j..i of x. The representative is truncated first:
// for i ≥ n the rule would otherwise read bits above n and break compatibility.
symbol extract [n] (i j : ℕ) : τ (bitvec n) → τ (bitvec (i - j + 1));
rule @extract $n $i $j (cl $x) ↪ class (≈ ($i - $j + 1)) (trunc ($i - $j + 1) (trunc $n $x >>> $j));

symbol zero_extend [n] (k : ℕ) : τ (bitvec n) → τ (bitvec (k + n));
rule @zero_extend $n $k (cl $x) ↪ class (≈ ($k + $n)) (trunc $n $x);

// Unsigned comparisons, as propositions on representatives.
symbol bvult [n] (x y : τ (bitvec n)) : Prop ≔ istrue (repr x < repr y);
symbol bvule [n] (x y : τ (bitvec n)) : Prop ≔ istrue (repr x ≤ repr y);
symbol bvugt [n] (x y : τ (bitvec n)) : Prop ≔ istrue (repr x > repr y);
symbol bvuge [n] (x y : τ (bitvec n)) : Prop ≔ istrue (repr x ≥ repr y);

// Signed comparisons: flipping the most significant bit turns the signed order
// into the unsigned one, so no integers are needed.
symbol flip [n] (x : τ (bitvec n)) : ℕ ≔ trunc n (repr x + 2 ^ (n ∸1));
symbol bvslt [n] (x y : τ (bitvec n)) : Prop ≔ istrue (flip x < flip y);
symbol bvsle [n] (x y : τ (bitvec n)) : Prop ≔ istrue (flip x ≤ flip y);
symbol bvsgt [n] (x y : τ (bitvec n)) : Prop ≔ istrue (flip x > flip y);
symbol bvsge [n] (x y : τ (bitvec n)) : Prop ≔ istrue (flip x ≥ flip y);

/* ------------------------------------------------------------------------
   List-level operations on digit lists (closed computation on literals) and
   on proposition lists (cvc5's bit-blasting shapes). All of them are total.
   ------------------------------------------------------------------------ */

// Cellwise Boolean operation on the n low digits; a missing digit reads false.
symbol zipbits : (𝔹 → 𝔹 → 𝔹) → ℕ → 𝕃 bool → 𝕃 bool → 𝕃 bool;
rule zipbits _ 0 _ _ ↪ □
with zipbits $op ($n +1) ($a ⸬ $l) ($b ⸬ $m) ↪ ($op $a $b) ⸬ zipbits $op $n $l $m
with zipbits $op ($n +1) □ ($b ⸬ $m) ↪ ($op false $b) ⸬ zipbits $op $n □ $m
with zipbits $op ($n +1) ($a ⸬ $l) □ ↪ ($op $a false) ⸬ zipbits $op $n $l □
with zipbits $op ($n +1) □ □ ↪ ($op false false) ⸬ zipbits $op $n □ □;

// Ripple-carry addition of two digit lists with a carry-in; the carry-out is
// appended as the last digit (so `take n` of it is addition modulo 2ⁿ).
symbol adc : 𝕃 bool → 𝕃 bool → 𝔹 → 𝕃 bool;
rule adc □ □ $c ↪ $c ⸬ □
with adc ($a ⸬ $l) ($b ⸬ $m) $c ↪ (($a xorb $b) xorb $c) ⸬ adc $l $m ((Stdlib.Bool.or) ((Stdlib.Bool.and) $a $b) ((Stdlib.Bool.and) ($a xorb $b) $c))
with adc □ ($b ⸬ $m) $c ↪ ($b xorb $c) ⸬ adc □ $m ((Stdlib.Bool.and) $b $c)
with adc ($a ⸬ $l) □ $c ↪ ($a xorb $c) ⸬ adc $l □ ((Stdlib.Bool.and) $a $c);

// cvc5's ripple-carry adder on propositions (bv_bitblast_step_bvadd), bit i is
// `xor (xor aᵢ bᵢ) cᵢ`, c₀ = ⊥, cᵢ₊₁ = (aᵢ ∧ bᵢ) ∨ ((xor aᵢ bᵢ) ∧ cᵢ).
symbol rca : 𝕃 o → 𝕃 o → Prop → 𝕃 o;
rule rca □ □ _ ↪ □
with rca ($a ⸬ $l) ($b ⸬ $m) $c ↪ (xor (xor $a $b) $c) ⸬ rca $l $m (($a ∧ $b) ∨ ((xor $a $b) ∧ $c));

// cvc5's bit-blasting of a variable: bit_of 0 x ⸬ … ⸬ bit_of (n-1) x ⸬ □.
symbol bitlist_from [n] : ℕ → ℕ → τ (bitvec n) → 𝕃 o;
rule @bitlist_from _ _ 0 _ ↪ □
with @bitlist_from $n $i ($k +1) $x ↪ (@bit_of $n $i $x) ⸬ (@bitlist_from $n ($i +1) $k $x);
symbol bitlist [n] (x : τ (bitvec n)) : 𝕃 o ≔ bitlist_from 0 n x;

// cvc5's bit-blasting of an equality: `a = b` for one bit, `(a = b) ∧ …`
// otherwise, no trailing ⊤ (the two patterns are disjoint).
symbol bbeq : 𝕃 o → 𝕃 o → Prop;
rule bbeq ($a ⸬ □) ($b ⸬ □) ↪ ($a = $b)
with bbeq ($a ⸬ $a' ⸬ $l) ($b ⸬ $b' ⸬ $m) ↪ ($a = $b) ∧ bbeq ($a' ⸬ $l) ($b' ⸬ $m);


/* ------------------------------------------------------------------------
   Parity, halving and truncation basics
   ------------------------------------------------------------------------ */

opaque symbol bit_cases x : π (bit x = 0 ∨ bit x = 1) ≔
begin
  assume x; simplify bit;
  apply ∨ₑ (case_𝔹 (odd x))
  { assume h; rewrite h; apply ∨ᵢ₂; reflexivity }
  { assume h; rewrite h; apply ∨ᵢ₁; reflexivity }
end;

opaque symbol bit_le1 x : π (istrue (bit x ≤ 1)) ≔
begin
  assume x; simplify bit;
  apply ∨ₑ (case_𝔹 (odd x))
  { assume h; rewrite h; apply ⊤ᵢ }
  { assume h; rewrite h; apply ⊤ᵢ }
end;

opaque symbol bit_div2 x : π (bit x + 2 * div2 x = x) ≔
begin
  assume x; simplify bit;
  apply ∨ₑ (case_𝔹 (odd x))
  { assume h; rewrite h; refine odd_div2 x (true=istrue h) }
  { assume h; rewrite h;
    have he : π (even x) { rewrite even_odd; rewrite h; apply ⊤ᵢ };
    refine even_div2 x he }
end;

opaque symbol odd_add_double a k : π (odd (a + 2 * k) = odd a) ≔
begin
  assume a; induction
  { reflexivity }
  { assume k ih; refine ih }
end;

opaque symbol div2_add_double a k : π (div2 (a + 2 * k) = div2 a + k) ≔
begin
  assume a; induction
  { reflexivity }
  { assume k ih; refine feq (+1) ih }
end;

opaque symbol odd_bit_double x y : π (odd (bit x + 2 * y) = odd x) ≔
begin
  assume x y; rewrite odd_add_double; simplify bit;
  apply ∨ₑ (case_𝔹 (odd x))
  { assume h; rewrite h; reflexivity }
  { assume h; rewrite h; reflexivity }
end;

opaque symbol div2_bit_double x y : π (div2 (bit x + 2 * y) = y) ≔
begin
  assume x y; rewrite div2_add_double; simplify bit;
  apply ∨ₑ (case_𝔹 (odd x))
  { assume h; rewrite h; reflexivity }
  { assume h; rewrite h; reflexivity }
end;

opaque symbol bit_eq x y : π (odd x = odd y) → π (bit x = bit y) ≔
begin
  assume x y h; change π (if (odd x) 1 0 = if (odd y) 1 0); rewrite h; reflexivity
end;

opaque symbol odd_trunc n x : π (odd (trunc (n +1) x) = odd x) ≔
begin
  assume n x; refine odd_bit_double x (trunc n (div2 x))
end;

opaque symbol div2_trunc n x : π (div2 (trunc (n +1) x) = trunc n (div2 x)) ≔
begin
  assume n x; refine div2_bit_double x (trunc n (div2 x))
end;

opaque symbol trunc_0 n : π (trunc n 0 = 0) ≔
begin
  induction
  { reflexivity }
  { assume n ih; simplify; rewrite ih; reflexivity }
end;

opaque symbol testbit_trunc_lt n x i : π (istrue (i < n)) → π (testbit (trunc n x) i = testbit x i) ≔
begin
  induction
  { assume x i h; apply ⊥ₑ (ltn0 i h) }
  { assume n ih x; induction
    { assume h; refine odd_trunc n x }
    { assume i ihi h;
      refine ind_eq (div2_trunc n x) (λ z, testbit z i = testbit (div2 x) i) (ih (div2 x) i h) } }
end;

opaque symbol testbit_trunc_ge n x i : π (istrue (n ≤ i)) → π (testbit (trunc n x) i = false) ≔
begin
  induction
  { assume x i h; refine testbit_0_l i }
  { assume n ih x; induction
    { assume h; apply ⊥ₑ h }
    { assume i ihi h;
      refine ind_eq (div2_trunc n x) (λ z, testbit z i = false) (ih (div2 x) i h) } }
end;

opaque symbol trunc_idem n x : π (trunc n (trunc n x) = trunc n x) ≔
begin
  induction
  { assume x; reflexivity }
  { assume n ih x;
    change π (bit (trunc (n +1) x) + 2 * trunc n (div2 (trunc (n +1) x)) = trunc (n +1) x);
    rewrite div2_trunc; rewrite ih; rewrite (bit_eq (trunc (n +1) x) x (odd_trunc n x)); reflexivity }
end;

opaque symbol odd_shiftr t i : π (odd (t >>> i) = testbit t i) ≔
begin
  assume t i; refine shiftr_spec t i 0
end;

opaque symbol shiftr_div2 n x : π (div2 (x >>> n) = div2 x >>> n) ≔
begin
  induction
  { assume x; reflexivity }
  { assume n ih x; refine feq div2 (ih x) }
end;

/* ------------------------------------------------------------------------
   Propositions as bits
   ------------------------------------------------------------------------ */

/* ------------------------------------------------------------------------
   Propositions as bits: `pb : Prop → 𝔹` and `istrue : 𝔹 → Prop` are
   mutually inverse, and `pb` is a homomorphism for ¬ ∧ ∨ xor.
   ------------------------------------------------------------------------ */

opaque symbol prop_2val p : π (p = ⊤ ∨ p = ⊥) ≔
begin
  assume p; apply ∨ₑ (em p)
  { assume hp; apply ∨ᵢ₁; apply eq_⊤_intro p hp }
  { assume hnp; apply ∨ᵢ₂; apply eq_⊥_intro p hnp }
end;

opaque symbol istrue_pb p : π (istrue (pb p) = p) ≔
begin
  assume p; apply ∨ₑ (prop_2val p)
  { assume h; rewrite h; reflexivity }
  { assume h; rewrite h; reflexivity }
end;

opaque symbol pb_istrue b : π (pb (istrue b) = b) ≔
begin
  assume b; apply ∨ₑ (case_𝔹 b)
  { assume h; rewrite h; reflexivity }
  { assume h; rewrite h; reflexivity }
end;

opaque symbol pb_inj p q : π (pb p = pb q) → π (p = q) ≔
begin
  assume p q h;
  rewrite left (istrue_pb p); rewrite left (istrue_pb q);
  rewrite h; reflexivity
end;

opaque symbol pb_⊤ p : π p → π (pb p = true) ≔
begin
  assume p h; rewrite (eq_⊤_intro p h); reflexivity
end;

opaque symbol pb_⊥ p : π (¬ p) → π (pb p = false) ≔
begin
  assume p h; rewrite (eq_⊥_intro p h); reflexivity
end;

// `pb` is a homomorphism for the connectives: two-valued case analysis, each
// case closed by `pb_⊤`/`pb_⊥` and a direct proof of the proposition.
opaque symbol pb_not p : π (pb (¬ p) = Stdlib.Bool.not (pb p)) ≔
begin
  assume p; apply ∨ₑ (prop_2val p)
  { assume h; rewrite h; apply pb_⊥ (¬ ⊤); assume h1; apply h1 ⊤ᵢ }
  { assume h; rewrite h; apply pb_⊤ (¬ ⊥); assume h1; apply h1 }
end;

opaque symbol pb_and p q : π (pb (p ∧ q) = (Stdlib.Bool.and) (pb p) (pb q)) ≔
begin
  assume p q; apply ∨ₑ (prop_2val p)
  { assume hp; rewrite hp; apply ∨ₑ (prop_2val q)
    { assume hq; rewrite hq; apply pb_⊤ (⊤ ∧ ⊤); apply ∧ᵢ ⊤ᵢ ⊤ᵢ }
    { assume hq; rewrite hq; apply pb_⊥ (⊤ ∧ ⊥); assume h; apply ∧ₑ₂ h } }
  { assume hp; rewrite hp; apply ∨ₑ (prop_2val q)
    { assume hq; rewrite hq; apply pb_⊥ (⊥ ∧ ⊤); assume h; apply ∧ₑ₁ h }
    { assume hq; rewrite hq; apply pb_⊥ (⊥ ∧ ⊥); assume h; apply ∧ₑ₁ h } }
end;

opaque symbol pb_or p q : π (pb (p ∨ q) = (Stdlib.Bool.or) (pb p) (pb q)) ≔
begin
  assume p q; apply ∨ₑ (prop_2val p)
  { assume hp; rewrite hp; apply ∨ₑ (prop_2val q)
    { assume hq; rewrite hq; apply pb_⊤ (⊤ ∨ ⊤); apply ∨ᵢ₁ ⊤ᵢ }
    { assume hq; rewrite hq; apply pb_⊤ (⊤ ∨ ⊥); apply ∨ᵢ₁ ⊤ᵢ } }
  { assume hp; rewrite hp; apply ∨ₑ (prop_2val q)
    { assume hq; rewrite hq; apply pb_⊤ (⊥ ∨ ⊤); apply ∨ᵢ₂ ⊤ᵢ }
    { assume hq; rewrite hq; apply pb_⊥ (⊥ ∨ ⊥); assume h;
      apply ∨ₑ h { assume h1; apply h1 } { assume h1; apply h1 } } }
end;

opaque symbol pb_xor p q : π (pb (xor p q) = (pb p) xorb (pb q)) ≔
begin
  assume p q; apply ∨ₑ (prop_2val p)
  { assume hp; rewrite hp; apply ∨ₑ (prop_2val q)
    { assume hq; rewrite hq; apply pb_⊥ (xor ⊤ ⊤); assume h;
      apply ∨ₑ h { assume h1; apply ∧ₑ₁ h1 ⊤ᵢ } { assume h1; apply ∧ₑ₂ h1 ⊤ᵢ } }
    { assume hq; rewrite hq; apply pb_⊤ (xor ⊤ ⊥);
      apply ∨ᵢ₂; apply ∧ᵢ { apply ⊤ᵢ } { assume x; apply x } } }
  { assume hp; rewrite hp; apply ∨ₑ (prop_2val q)
    { assume hq; rewrite hq; apply pb_⊤ (xor ⊥ ⊤);
      apply ∨ᵢ₁; apply ∧ᵢ { assume x; apply x } { apply ⊤ᵢ } }
    { assume hq; rewrite hq; apply pb_⊥ (xor ⊥ ⊥); assume h;
      apply ∨ₑ h { assume h1; apply ∧ₑ₂ h1 } { assume h1; apply ∧ₑ₁ h1 } } }
end;

opaque symbol istrue_inj a b : π (istrue a = istrue b) → π (a = b) ≔
begin
  assume a b h;
  rewrite left (pb_istrue a); rewrite left (pb_istrue b);
  rewrite h; reflexivity
end;

opaque symbol map_pb_istrue (l : 𝕃 bool) : π (map pb (map istrue l) = l) ≔
begin
  induction
  { reflexivity }
  { assume x l ih; simplify; rewrite ih; rewrite pb_istrue; reflexivity }
end;

/* ------------------------------------------------------------------------
   Size bounds
   ------------------------------------------------------------------------ */

/* ------------------------------------------------------------------------
   Group "size bounds of truncation and bitwise".
   ------------------------------------------------------------------------ */

// A digit `if c 1 0` is at most 1 (both cases compute).
opaque symbol if_le1 (c : 𝔹) : π (istrue ((if c 1 0) ≤ 1)) ≔
begin
  induction
  { refine ⊤ᵢ }
  { refine ⊤ᵢ }
end;

// `bit x ≡ if (odd x) 1 0`, so this is `if_le1 (odd x)` by conversion.

// The one-step bound: a digit plus twice something below m stays below 2m.
// `c + 2 * t < m + m` is `(c + (t + t)) +1 ≤ m + m` by conversion, and
// `1 + ((t + t) +1) ≡ (t +1) + (t +1)`.
opaque symbol lt_double_step c t m :
  π (istrue (c ≤ 1)) → π (istrue (t < m)) → π (istrue (c + 2 * t < m + m)) ≔
begin
  assume c t m hc ht;
  have h1 : π (istrue (c + ((t + t) +1) ≤ 1 + ((t + t) +1)))
    { refine leq_add c ((t + t) +1) 1 ((t + t) +1) hc (≤_refl ((t + t) +1)) };
  have h2 : π (istrue ((t +1) + (t +1) ≤ m + m))
    { refine leq_add (t +1) (t +1) m m ht ht };
  refine @leq_trans (c + ((t + t) +1)) (1 + ((t + t) +1)) (m + m) h1 h2
end;

opaque symbol pow2_gt0 n : π (istrue (0 < 2 ^ n)) ≔
begin
  induction
  { refine ⊤ᵢ }
  { assume n ih; refine ltn_addr 0 (2 ^ n) (2 ^ n) ih }
end;

// Induction on m with x general; x is then split 0 / 1 / x+2, and every
// case is a computation (`(m +1) + (m +1) ≡ ((m + m) +1) +1`).
opaque symbol div2_lt_double x m : π (istrue (x < m + m)) → π (istrue (div2 x < m)) ≔
begin
  have aux : Π m x, π (istrue (x < m + m)) → π (istrue (div2 x < m))
  { induction
    { assume x h; refine ⊥ₑ (ltn0 x h) }
    { assume m ih;
      refine ind_ℕ2 (λ x, istrue (x < (m +1) + (m +1)) ⇒ istrue (div2 x < m +1)) _ _ _
      { assume h; refine ⊤ᵢ }
      { assume h; refine ⊤ᵢ }
      { assume x h0 h1 h; refine ih x h } } };
  assume x m; refine aux m x
end;

opaque symbol lt_pow2_div2 n x : π (istrue (x < 2 ^ (n +1))) → π (istrue (div2 x < 2 ^ n)) ≔
begin
  assume n x h; refine div2_lt_double x (2 ^ n) h
end;

opaque symbol trunc_lt n x : π (istrue (trunc n x < 2 ^ n)) ≔
begin
  induction
  { assume x; refine ⊤ᵢ }
  { assume n ih x;
    refine lt_double_step (bit x) (trunc n (div2 x)) (2 ^ n) (bit_le1 x) (ih (div2 x)) }
end;

// x is its low bit plus twice its half. Two-step induction: `bit (x +1 +1)`
// converts to `bit x` (even (x +1 +1) ↪ even x) and `div2 (x +1 +1)` to
// `div2 x +1`, so the step is the hypothesis under `+1 +1`.

opaque symbol trunc_small n x : π (istrue (x < 2 ^ n)) → π (trunc n x = x) ≔
begin
  induction
  { assume x h; symmetry; refine ≤0 x h }
  { assume n ih x h;
    refine ind_eq (ih (div2 x) (lt_pow2_div2 n x h)) (λ z, bit x + 2 * z = x) (bit_div2 x) }
end;

opaque symbol bitwise_lt op n a b : π (istrue (bitwise op n a b < 2 ^ n)) ≔
begin
  assume op; induction
  { assume a b; refine ⊤ᵢ }
  { assume n ih a b;
    refine lt_double_step (if (op (odd a) (odd b)) 1 0) (bitwise op n (div2 a) (div2 b)) (2 ^ n)
      (if_le1 (op (odd a) (odd b))) (ih (div2 a) (div2 b)) }
end;

/* ------------------------------------------------------------------------
   Bit extensionality on ℕ
   ------------------------------------------------------------------------ */

/* ------------------------------------------------------------------------
   Group 3: bit extensionality. A natural number is determined by its bits,
   and the low n bits determine (and are determined by) `trunc n`.
   ------------------------------------------------------------------------ */

// ---- helpers ----

// `odd x = false` read as `even x = true`.
opaque symbol odd_false_even x : π (odd x = false) → π (even x = true) ≔
begin
  assume x h; rewrite even_odd; rewrite h; reflexivity
end;

// Bounded form of testbit_all_false: induction on a bound k ≥ y, halving y.
opaque symbol testbit_all_false_bnd k : Π y, π (istrue (y ≤ k)) → (Π i, π (testbit y i = false)) → π (y = 0) ≔
begin
  induction
  { assume y hle hall; refine ≤0 y hle }
  { assume k ih y hle hall;
    have h0 : π (odd y = false) { refine hall 0 };
    have hd : π (div2 y + div2 y = y) { refine even_div2 y (true=istrue (odd_false_even y h0)) };
    have hd0 : π (div2 y = 0) { refine ih (div2 y) (leq_div2_leqS y k hle) (λ i, hall (i +1)) };
    rewrite left hd; rewrite hd0; reflexivity }
end;

// ---- requested lemmas ----

opaque symbol testbit_all_false y : (Π i, π (testbit y i = false)) → π (y = 0) ≔
begin
  assume y h; refine testbit_all_false_bnd y y (≤_refl y) h
end;

// Bounded form of testbit_ext: induction on a bound k ≥ x, halving both.
opaque symbol testbit_ext_bnd k : Π x y, π (istrue (x ≤ k)) → (Π i, π (testbit x i = testbit y i)) → π (x = y) ≔
begin
  induction
  { assume x y hle hall;
    have hx : π (x = 0) { refine ≤0 x hle };
    rewrite hx; symmetry; apply testbit_all_false; assume i;
    rewrite left (hall i); rewrite hx; refine testbit_0_l i }
  { assume k ih x y hle hall;
    have h0 : π (odd x = odd y) { refine hall 0 };
    have hd : π (div2 x = div2 y)
      { refine ih (div2 x) (div2 y) (leq_div2_leqS x k hle) (λ i, hall (i +1)) };
    apply ∨ₑ (case_𝔹 (odd x))
    { assume hox;
      have hoy : π (odd y = true) { rewrite left h0; refine hox };
      have hx : π ((div2 x + div2 x) +1 = x) { refine odd_div2 x (true=istrue hox) };
      have hy : π ((div2 y + div2 y) +1 = y) { refine odd_div2 y (true=istrue hoy) };
      rewrite left hx; rewrite left hy; rewrite hd; reflexivity }
    { assume hox;
      have hoy : π (odd y = false) { rewrite left h0; refine hox };
      have hx : π (div2 x + div2 x = x) { refine even_div2 x (true=istrue (odd_false_even x hox)) };
      have hy : π (div2 y + div2 y = y) { refine even_div2 y (true=istrue (odd_false_even y hoy)) };
      rewrite left hx; rewrite left hy; rewrite hd; reflexivity } }
end;

opaque symbol testbit_ext x y : (Π i, π (testbit x i = testbit y i)) → π (x = y) ≔
begin
  assume x y h; refine testbit_ext_bnd x x y (≤_refl x) h
end;

opaque symbol trunc_ext n x y : (Π i, π (istrue (i < n)) → π (testbit x i = testbit y i)) → π (trunc n x = trunc n y) ≔
begin
  induction
  { assume x y h; reflexivity }
  { assume n ih x y h;
    have h0 : π (odd x = odd y) { refine h 0 ⊤ᵢ };
    have hb : π (bit x = bit y)
      { change π ((if (odd x) 1 0) = (if (odd y) 1 0)); rewrite h0; reflexivity };
    have hr : π (trunc n (div2 x) = trunc n (div2 y))
      { refine ih (div2 x) (div2 y) (λ i hi, h (i +1) hi) };
    change π (bit x + 2 * trunc n (div2 x) = bit y + 2 * trunc n (div2 y));
    rewrite hb; rewrite hr; reflexivity }
end;

// The parity of `bit x + 2 * t` is the parity of x.

// Halving `bit x + 2 * t` gives t.

// Bits below the width survive truncation.

opaque symbol trunc_testbit n x y : π (trunc n x = trunc n y) → Π i, π (istrue (i < n)) → π (testbit x i = testbit y i) ≔
begin
  assume n x y h i hi;
  rewrite left (testbit_trunc_lt n x i hi);
  rewrite left (testbit_trunc_lt n y i hi);
  rewrite h; reflexivity
end;

/* ------------------------------------------------------------------------
   Arithmetic modulo 2ⁿ
   ------------------------------------------------------------------------ */

/* ------------------------------------------------------------------------
   Group 4: arithmetic modulo 2^n.
   odd_add_double, div2_add_double.
   ------------------------------------------------------------------------ */

// div2 commutes with right shift.

// A number is its low bit plus twice its half.

// Adding a double does not change parity …
opaque symbol odd_addnn_l k a : π (odd (k + k + a) = odd a) ≔
begin
  induction
  { assume a; reflexivity }
  { assume k ih a; refine ih a }
end;

// … and shifts the half by k.
opaque symbol div2_addnn_l k a : π (div2 (k + k + a) = div2 a + k) ≔
begin
  induction
  { assume a; reflexivity }
  { assume k ih a; refine feq (+1) (ih a) }
end;

opaque symbol div_mod_pow2 n x : π (trunc n x + 2 ^ n * (x >>> n) = x) ≔
begin
  induction
  { assume x; reflexivity }
  { assume n ih x;
    have e : π (bit x + (2 * trunc n (div2 x) + 2 * 2 ^ n * div2 (x >>> n)) = x)
    { rewrite shiftr_div2 n x;
      rewrite mulnA 2 (2 ^ n) (div2 x >>> n);
      rewrite left (mulnDr (trunc n (div2 x)) (2 ^ n * (div2 x >>> n)) 2);
      rewrite ih (div2 x);
      refine bit_div2 x };
    refine e }
end;

opaque symbol trunc_add_pow2 n a q : π (trunc n (a + 2 ^ n * q) = trunc n a) ≔
begin
  induction
  { assume a q; reflexivity }
  { assume n ih a q;
    have e : π (a + 2 ^ (n +1) * q = 2 ^ n * q + 2 ^ n * q + a)
    { rewrite addnC a (2 ^ (n +1) * q);
      rewrite expnS 2 n;
      rewrite mulnA 2 (2 ^ n) q;
      reflexivity };
    rewrite e;
    have hd : π (div2 (2 ^ n * q + 2 ^ n * q + a) = div2 a + 2 ^ n * q)
    { refine div2_addnn_l (2 ^ n * q) a };
    have hb : π (bit (2 ^ n * q + 2 ^ n * q + a) = bit a)
    { change π (if (odd (2 ^ n * q + 2 ^ n * q + a)) 1 0 = if (odd a) 1 0);
      rewrite odd_addnn_l (2 ^ n * q) a; reflexivity };
    change π (bit (2 ^ n * q + 2 ^ n * q + a) + 2 * trunc n (div2 (2 ^ n * q + 2 ^ n * q + a)) = bit a + 2 * trunc n (div2 a));
    rewrite hd; rewrite hb; rewrite ih (div2 a) q; reflexivity }
end;

// trunc n absorbs truncation of either summand: x + y = (trunc n x + y) + 2^n * (x >>> n).
opaque symbol trunc_add_l n x y : π (trunc n (x + y) = trunc n (trunc n x + y)) ≔
begin
  assume n x y;
  have e : π (trunc n x + (y + 2 ^ n * (x >>> n)) = x + y)
  { rewrite addnC y (2 ^ n * (x >>> n));
    refine feq (λ z, z + y) (div_mod_pow2 n x) };
  rewrite left (trunc_add_pow2 n (trunc n x + y) (x >>> n));
  refine feq (trunc n) (eq_sym e)
end;

opaque symbol trunc_add_r n x y : π (trunc n (x + y) = trunc n (x + trunc n y)) ≔
begin
  assume n x y;
  rewrite addnC x y; rewrite addnC x (trunc n y);
  refine trunc_add_l n y x
end;

opaque symbol trunc_add_lr n x y : π (trunc n (x + y) = trunc n (trunc n x + trunc n y)) ≔
begin
  assume n x y;
  rewrite trunc_add_l n x y;
  refine trunc_add_r n (trunc n x) y
end;

// Same for products: x * y = trunc n x * y + 2^n * ((x >>> n) * y).
opaque symbol trunc_mul_l n x y : π (trunc n (x * y) = trunc n (trunc n x * y)) ≔
begin
  assume n x y;
  have e : π (trunc n x * y + 2 ^ n * ((x >>> n) * y) = x * y)
  { rewrite left (mulnA (2 ^ n) (x >>> n) y);
    rewrite left (mulnDl (trunc n x) (2 ^ n * (x >>> n)) y);
    rewrite div_mod_pow2 n x; reflexivity };
  rewrite left (trunc_add_pow2 n (trunc n x * y) ((x >>> n) * y));
  refine feq (trunc n) (eq_sym e)
end;

opaque symbol trunc_mul_r n x y : π (trunc n (x * y) = trunc n (x * trunc n y)) ≔
begin
  assume n x y;
  rewrite mulnC x y; rewrite mulnC x (trunc n y);
  refine trunc_mul_l n y x
end;

/* ------------------------------------------------------------------------
   Digit lists
   ------------------------------------------------------------------------ */

/* ---------------- helpers (group g5: digit lists) ---------------- */

// trunc n 0 = 0

// parity and halving of a digit prepended to a doubled number
opaque symbol odd_digit b x : π (odd ((if b 1 0) + 2 * x) = b) ≔
begin
  assume b x; apply ∨ₑ (case_𝔹 b)
  { assume hb; rewrite hb; refine istrue=true (odd_addnnS x) }
  { assume hb; rewrite hb; change π (not (even (x + x)) = false);
    rewrite (istrue=true (even_addnn x)); reflexivity }
end;

opaque symbol div2_digit b x : π (div2 ((if b 1 0) + 2 * x) = x) ≔
begin
  assume b x; apply ∨ₑ (case_𝔹 b)
  { assume hb; rewrite hb; refine div2_addnnS x }
  { assume hb; rewrite hb; refine div2_addnn x }
end;

opaque symbol bit_digit b x : π (bit ((if b 1 0) + 2 * x) = if b 1 0) ≔
begin
  assume b x; change π ((if (odd ((if b 1 0) + 2 * x)) 1 0) = if b 1 0);
  rewrite odd_digit; reflexivity
end;

opaque symbol trunc_digit n b x :
  π (trunc (n +1) ((if b 1 0) + 2 * x) = (if b 1 0) + 2 * trunc n x) ≔
begin
  assume n b x;
  change π (bit ((if b 1 0) + 2 * x) + 2 * trunc n (div2 ((if b 1 0) + 2 * x))
            = (if b 1 0) + 2 * trunc n x);
  rewrite bit_digit; rewrite div2_digit; reflexivity
end;

/* ---------------- requested lemmas ---------------- */

opaque symbol bits2natB_nseq_false n : π (bits2natB (nseq n false) = 0) ≔
begin
  induction
  { reflexivity }
  { assume n ih; simplify; rewrite ih; reflexivity }
end;

opaque symbol bits2natB_cat l m : π (bits2natB (l ++ m) = bits2natB l + 2 ^ (size l) * bits2natB m) ≔
begin
  induction
  { assume m; reflexivity }
  { assume b l ih m;
    change π ((if b 1 0) + 2 * bits2natB (l ++ m)
              = (if b 1 0) + 2 * bits2natB l + (2 * 2 ^ (size l)) * bits2natB m);
    rewrite ih m; rewrite mulnDr; rewrite mulnA; reflexivity }
end;

opaque symbol bits2natB_lt l : π (istrue (bits2natB l < 2 ^ (size l))) ≔
begin
  induction
  { apply ⊤ᵢ }
  { assume b l ih;
    have h : π (istrue ((bits2natB l +1) + (bits2natB l +1) ≤ 2 ^ (size l) + 2 ^ (size l)))
      { refine leq_add (bits2natB l +1) (bits2natB l +1) (2 ^ (size l)) (2 ^ (size l)) ih ih };
    apply ∨ₑ (case_𝔹 b)
    { assume hb; rewrite hb; refine h }
    { assume hb; rewrite hb;
      refine ltnW ((bits2natB l + bits2natB l) +1) (2 ^ (size l) + 2 ^ (size l)) h } }
end;

opaque symbol trunc_bits2natB n l : π (trunc n (bits2natB l) = bits2natB (take n l)) ≔
begin
  induction
  { assume l; reflexivity }
  { assume n ih; induction
    { change π (bit 0 + 2 * trunc n 0 = 0); rewrite trunc_0; reflexivity }
    { assume b l ihl;
      change π (trunc (n +1) ((if b 1 0) + 2 * bits2natB l) = (if b 1 0) + 2 * bits2natB (take n l));
      rewrite trunc_digit; rewrite ih l; reflexivity } }
end;

opaque symbol testbit_bits2natB l i : π (testbit (bits2natB l) i = nth false l i) ≔
begin
  induction
  { assume i; refine testbit_0_l i }
  { assume b l ih; induction
    { refine odd_digit b (bits2natB l) }
    { assume i ihi;
      change π (testbit (div2 ((if b 1 0) + 2 * bits2natB l)) i = nth false l i);
      rewrite div2_digit; refine ih i } }
end;

// injectivity of a digit prepended to a doubled number
opaque symbol digit_inj_hd ea eb x y :
  π ((if ea 1 0) + 2 * x = (if eb 1 0) + 2 * y) → π (ea = eb) ≔
begin
  assume ea eb x y h;
  rewrite left (odd_digit ea x); rewrite left (odd_digit eb y);
  refine feq odd h
end;

opaque symbol digit_inj_tl ea eb x y :
  π ((if ea 1 0) + 2 * x = (if eb 1 0) + 2 * y) → π (x = y) ≔
begin
  assume ea eb x y h;
  rewrite left (div2_digit ea x); rewrite left (div2_digit eb y);
  refine feq div2 h
end;

opaque symbol bits2natB_inj l m : π (size l = size m) → π (bits2natB l = bits2natB m) → π (l = m) ≔
begin
  assume l m hs;
  refine seq_ind2 (λ la lb, bits2natB la = bits2natB lb ⇒ la = lb) _ _ l m hs
  { assume h; reflexivity }
  { assume la lb ea eb hs2 ih he;
    have h1 : π (ea = eb) { refine digit_inj_hd ea eb (bits2natB la) (bits2natB lb) he };
    have h2 : π (la = lb) { apply ih; refine digit_inj_tl ea eb (bits2natB la) (bits2natB lb) he };
    rewrite h1; rewrite h2; reflexivity }
end;

opaque symbol size_fit n l : π (size (fit n l) = n) ≔
begin
  assume n l; apply size_takel n (l ++ nseq n false);
  rewrite size_cat; rewrite size_nseq; apply leq_addl (size l) n
end;

opaque symbol bits2natB_fit n l : π (bits2natB (fit n l) = trunc n (bits2natB l)) ≔
begin
  assume n l;
  change π (bits2natB (take n (l ++ nseq n false)) = trunc n (bits2natB l));
  rewrite left (trunc_bits2natB n (l ++ nseq n false));
  rewrite bits2natB_cat; rewrite bits2natB_nseq_false; rewrite muln0; reflexivity
end;

opaque symbol fit_size l : π (fit (size l) l = l) ≔
begin
  assume l; apply take_size_cat (size l) l (nseq (size l) false); reflexivity
end;

opaque symbol take_fit n l : π (take n (fit n l) = fit n l) ≔
begin
  assume n l; apply take_oversize n (fit n l); rewrite size_fit; apply ≤_refl n
end;

opaque symbol nth_take [a] (x : τ a) n (l : 𝕃 a) i : π (istrue (i < n)) → π (nth x (take n l) i = nth x l i) ≔
begin
  assume a x; induction
  { assume l i h; refine ⊥ₑ h }
  { assume n ih; induction
    { assume i h; reflexivity }
    { assume e l ihl; induction
      { assume h; reflexivity }
      { assume i ihi h; refine ih l i h } } }
end;

// every element of nseq n x is x
opaque symbol nth_nseq [a] (x : τ a) n i : π (nth x (nseq n x) i = x) ≔
begin
  assume a x; induction
  { assume i; reflexivity }
  { assume n ih; induction
    { reflexivity }
    { assume i ihi; refine ih i } }
end;

opaque symbol nth_pad l n i : π (nth false (l ++ nseq n false) i = nth false l i) ≔
begin
  induction
  { assume n i; refine nth_nseq false n i }
  { assume e l ih n; induction
    { reflexivity }
    { assume i ihi; refine ih n i } }
end;

opaque symbol nth_fit n l i : π (istrue (i < n)) → π (nth false (fit n l) i = nth false l i) ≔
begin
  assume n l i h;
  change π (nth false (take n (l ++ nseq n false)) i = nth false l i);
  rewrite nth_take false n (l ++ nseq n false) i h;
  refine nth_pad l n i
end;

/* ------------------------------------------------------------------------
   Stdlib.Nat.bitwise with the width as fuel
   ------------------------------------------------------------------------ */

// ---- helpers (group 6: Stdlib.Nat.bitwise with the width as fuel) ----

// The parity of a digit followed by a doubled tail is the digit.

// Halving a digit followed by a doubled tail is the tail.

// ---- requested lemmas ----

opaque symbol odd_bitwise' op n a b : π (odd (bitwise op (n +1) a b) = op (odd a) (odd b)) ≔
begin
  assume op n a b;
  refine odd_digit (op (odd a) (odd b)) (bitwise op n (div2 a) (div2 b))
end;

opaque symbol div2_bitwise' op n a b : π (div2 (bitwise op (n +1) a b) = bitwise op n (div2 a) (div2 b)) ≔
begin
  assume op n a b;
  refine div2_digit (op (odd a) (odd b)) (bitwise op n (div2 a) (div2 b))
end;

// Induction on the fuel n, general in m a b (then m is split by cases).
opaque symbol testbit_bitwise_lt' op n m a b :
  π (istrue (m < n)) → π (testbit (bitwise op n a b) m = op (testbit a m) (testbit b m)) ≔
begin
  assume op; induction
  { assume m a b h; apply ⊥ₑ (ltn0 m h) }
  { assume n ih; induction
    { assume a b h; refine odd_bitwise' op n a b }
    { assume m ihm a b h;
      simplify testbit; rewrite div2_bitwise';
      refine ih m (div2 a) (div2 b) h } }
end;

opaque symbol testbit_bitwise_lt op n a b m : π (istrue (m < n)) → π (testbit (bitwise op n a b) m = op (testbit a m) (testbit b m)) ≔
begin
  assume op n a b m h; refine testbit_bitwise_lt' op n m a b h
end;

opaque symbol testbit_bitwise_ge' op n m a b :
  π (istrue (n ≤ m)) → π (testbit (bitwise op n a b) m = false) ≔
begin
  assume op; induction
  { assume m a b h; refine testbit_0_l m }
  { assume n ih; induction
    { assume a b h; apply ⊥ₑ h }
    { assume m ihm a b h;
      simplify testbit; rewrite div2_bitwise';
      refine ih m (div2 a) (div2 b) h } }
end;

opaque symbol testbit_bitwise_ge op n a b m : π (istrue (n ≤ m)) → π (testbit (bitwise op n a b) m = false) ≔
begin
  assume op n a b m h; refine testbit_bitwise_ge' op n m a b h
end;

// `trunc (n +1) a` is `bit a + 2 * trunc n (div2 a)`: its parity and half.


opaque symbol bitwise_trunc_l op n a b : π (bitwise op n (trunc n a) b = bitwise op n a b) ≔
begin
  assume op; induction
  { assume a b; reflexivity }
  { assume n ih a b;
    simplify bitwise;
    rewrite odd_trunc; rewrite div2_trunc; rewrite ih; reflexivity }
end;

opaque symbol bitwise_trunc_r op n a b : π (bitwise op n a (trunc n b) = bitwise op n a b) ≔
begin
  assume op; induction
  { assume a b; reflexivity }
  { assume n ih a b;
    simplify bitwise;
    rewrite odd_trunc; rewrite div2_trunc; rewrite ih; reflexivity }
end;

opaque symbol trunc_bitwise op n a b : π (trunc n (bitwise op n a b) = bitwise op n a b) ≔
begin
  assume op; induction
  { assume a b; reflexivity }
  { assume n ih a b;
    change π ((if (odd (bitwise op (n +1) a b)) 1 0)
              + 2 * trunc n (div2 (bitwise op (n +1) a b)) = bitwise op (n +1) a b);
    rewrite odd_bitwise'; rewrite div2_bitwise'; rewrite ih; reflexivity }
end;

/* ------------------------------------------------------------------------
   Representatives and bit extensionality on the quotient
   ------------------------------------------------------------------------ */

opaque symbol repr_class n v : π (repr (class (≈ n) v) = trunc n v) ≔
begin
  assume n v; reflexivity
end;

// Equal classes have equal canonical representatives: the quotient is
// effective, through `repr` (no `exact` axiom is needed).
opaque symbol cl_inj n u v : π (class (≈ n) u = class (≈ n) v) → π (trunc n u = trunc n v) ≔
begin
  assume n u v h; refine feq repr h
end;

// Transitivity as a term, for the proof terms the translator builds bit by bit.
opaque symbol eqt [a] [x y z : τ a] : π (x = y) → π (y = z) → π (x = z) ≔
begin
  assume a x y z h1 h2; rewrite h1; refine h2
end;

// `eqt` with its three terms explicit. rules/bv.rs inlines the tautology
// prover's term (`¬¬ₑ _ (tauto_aux ⊤ᵢ ⊤ᵢ)`) as the first proof, and the prover
// reifies its goal by rewriting: that goal, `x = y`, has to be fixed before the
// term is elaborated, which the explicit arguments do and `eqt`'s implicit ones
// would not (a metavariable would be reified as an atom).
opaque symbol eqt_e [a] (x y z : τ a) : π (x = y) → π (y = z) → π (x = z) ≔
begin
  assume a x y z h k; refine (eqt h k)
end;

// The conjunction of the bit equalities below k, as a computed proposition
// (the per-width shape a script can discharge bit by bit).
symbol bits_eq_upto [n] : ℕ → τ (bitvec n) → τ (bitvec n) → Prop;
rule @bits_eq_upto _ 0 _ _ ↪ ⊤
with @bits_eq_upto $n ($k +1) $x $y ↪ (@bit_of $n $k $x = @bit_of $n $k $y) ∧ @bits_eq_upto $n $k $x $y;

/* ------------------------------------------------------------------------
   Representatives, bit extensionality and the bit-blasting of a variable
   ------------------------------------------------------------------------ */

/* ------------------------------------------------------------------------
   Group "quot": representatives, bit extensionality on the quotient,
   bit-blasting of a variable.
   ------------------------------------------------------------------------ */

// The class of the canonical representative is the class itself.
opaque symbol class_repr [n] (x : τ (bitvec n)) : π (class (≈ n) (repr x) = x) ≔
begin
  assume n; induction; assume v;
  apply sound; simplify π;
  refine trunc_idem n v
end;

// `repr` is injective: the quotient is effective.
opaque symbol repr_inj [n] (x y : τ (bitvec n)) : π (repr x = repr y) → π (x = y) ≔
begin
  assume n x y h;
  rewrite left (class_repr x); rewrite left (class_repr y);
  rewrite h; reflexivity
end;

// Bit extensionality on the quotient: equal bits below the width, equal classes.
opaque symbol bv_ext [n] (x y : τ (bitvec n)) :
  (Π i, π (istrue (i < n)) → π (bit_of i x = bit_of i y)) → π (x = y) ≔
begin
  assume n; induction; assume u; induction; assume v h;
  apply sound; simplify π;
  refine trunc_ext n u v _; assume i hi;
  rewrite left (testbit_trunc_lt n u i hi);
  rewrite left (testbit_trunc_lt n v i hi);
  refine istrue_inj (testbit (trunc n u) i) (testbit (trunc n v) i) (h i hi)
end;

// ---- helper: `bits_eq_upto k` gives every bit below k ----
opaque symbol quot_bits_eq_upto_bit k n (x y : τ (bitvec n)) :
  π (bits_eq_upto k x y) → Π i, π (istrue (i < k)) → π (bit_of i x = bit_of i y) ≔
begin
  induction
  { assume n x y h i hi; apply ⊥ₑ (ltn0 i hi) }
  { assume k ih n x y h i hi;
    have hle : π ((i = k) ∨ istrue (i < k)) { refine ∧ₑ₁ (leq_eqVlt i k) hi };
    apply ∨ₑ hle
    { assume e; rewrite e; refine ∧ₑ₁ h }
    { assume lt; refine ih n x y (∧ₑ₂ h) i lt } }
end;

opaque symbol bv_ext_list [n] (x y : τ (bitvec n)) : π (bits_eq_upto n x y) → π (x = y) ≔
begin
  assume n x y h; apply bv_ext x y; assume i hi;
  refine quot_bits_eq_upto_bit n n x y h i hi
end;

opaque symbol size_bitlist_from n i k (x : τ (bitvec n)) : π (size (@bitlist_from n i k x) = k) ≔
begin
  assume n i k x;
  have aux : Π m j, π (size (@bitlist_from n j m x) = m)
  { induction
    { assume j; reflexivity }
    { assume m ih j; refine feq (+1) (ih (j +1)) } };
  refine aux k i
end;

opaque symbol bits2natB_bitlist n k : Π i v,
  π (bits2natB (map pb (@bitlist_from n i k (class (≈ n) v))) = trunc k (trunc n v >>> i)) ≔
begin
  assume n; induction
  { assume i v; reflexivity }
  { assume k ih i v;
    change π ((if (pb (istrue (testbit (trunc n v) i))) 1 0)
              + 2 * bits2natB (map pb (@bitlist_from n (i +1) k (class (≈ n) v)))
              = (if (odd (trunc n v >>> i)) 1 0) + 2 * trunc k (trunc n v >>> (i +1)));
    rewrite ih (i +1) v; rewrite pb_istrue; rewrite odd_shiftr; reflexivity }
end;

// cvc5's bit-blasting of a variable is the variable.
opaque symbol bb_var [n] (x : τ (bitvec n)) : π (x = bbterm n (bitlist x)) ≔
begin
  assume n; induction; assume v;
  symmetry; apply sound; simplify π;
  change π (trunc n (bits2natB (map pb (@bitlist_from n 0 n (class (≈ n) v)))) = trunc n v);
  rewrite (bits2natB_bitlist n n 0 v);
  rewrite (trunc_idem n (trunc n v >>> 0));
  refine trunc_idem n v
end;

// ---- helper: nth through `map pb` ----
opaque symbol quot_nth_map_pb (L : 𝕃 o) i : π (nth false (map pb L) i = pb (nth ⊥ L i)) ≔
begin
  induction
  { assume i; reflexivity }
  { assume p L ih; induction
    { reflexivity }
    { assume i ihi; refine ih i } }
end;

opaque symbol bit_of_bbterm n L i : π (istrue (i < n)) → π (bit_of i (bbterm n L) = nth ⊥ L i) ≔
begin
  assume n L i hi;
  change π (istrue (testbit (trunc n (bits2natB (map pb L))) i) = nth ⊥ L i);
  rewrite testbit_trunc_lt n (bits2natB (map pb L)) i hi;
  rewrite testbit_bits2natB;
  rewrite quot_nth_map_pb;
  refine istrue_pb (nth ⊥ L i)
end;

/* ------------------------------------------------------------------------
   cvc5's bit-blasting of an equality
   ------------------------------------------------------------------------ */

/* ------------------------------------------------------------------------
   Group "cvc5's equality conjunction": `bbterm n L = bbterm n M` is cvc5's
   `bbeq L M` (bit_blast_step for `=`), for n > 0 and |L| = |M| = n.
   ------------------------------------------------------------------------ */

// `map pb` is injective, because `pb` is (`pb_inj`). Induction on L with M
// general; the mismatched-shape cases are refuted through their sizes.
opaque symbol map_pb_inj L M : π (map pb L = map pb M) → π (L = M) ≔
begin
  induction
  { induction
    { assume h; reflexivity }
    { assume b M ihM h;
      have hs : π (0 = size (map pb M) +1) { refine feq size h };
      refine ⊥ₑ (0≠s hs) } }
  { assume a L ih; induction
    { assume h;
      have hs : π (size (map pb L) +1 = 0) { refine feq size h };
      refine ⊥ₑ (s≠0 hs) }
    { assume b M ihM h;
      have h1 : π (pb a = pb b) { refine ∧ₑ₁ (⸬_inj h) };
      have h2 : π (map pb L = map pb M) { refine ∧ₑ₂ (⸬_inj h) };
      rewrite (pb_inj a b h1); rewrite (ih M h2); reflexivity } }
end;

// ---- helpers ----

// `bbeq` is reflexive on a non-empty list: induction on the tail, so that the
// one-cell and the two-cell rules are each a computation.
opaque symbol bbeq_cons_refl L a : π (bbeq (a ⸬ L) (a ⸬ L)) ≔
begin
  induction
  { assume a; reflexivity }
  { assume a2 L2 ih a; apply ∧ᵢ { reflexivity } { refine ih a2 } }
end;

// `bbeq` on two non-empty lists of the same size forces the lists equal.
opaque symbol bbeq_cons_eq L M a b :
  π (size L = size M) → π (bbeq (a ⸬ L) (b ⸬ M)) → π (a ⸬ L = b ⸬ M) ≔
begin
  induction
  { induction
    { assume a b hs h; have e : π (a = b) { refine h }; rewrite e; reflexivity }
    { assume b2 M2 ihM a b hs h;
      have hs' : π (0 = size M2 +1) { refine hs };
      refine ⊥ₑ (0≠s hs') } }
  { assume a2 L2 ih; induction
    { assume a b hs h;
      have hs' : π (size L2 +1 = 0) { refine hs };
      refine ⊥ₑ (s≠0 hs') }
    { assume b2 M2 ihM a b hs h;
      have h' : π ((a = b) ∧ bbeq (a2 ⸬ L2) (b2 ⸬ M2)) { refine h };
      have hs' : π (size L2 +1 = size M2 +1) { refine hs };
      have e1 : π (a = b) { refine ∧ₑ₁ h' };
      have e2 : π (a2 ⸬ L2 = b2 ⸬ M2) { refine ih M2 a2 b2 (+1_inj hs') (∧ₑ₂ h') };
      rewrite e1; rewrite e2; reflexivity } }
end;

// ---- requested lemmas ----

opaque symbol bbeq_refl L : π (istrue (0 < size L)) → π (bbeq L L) ≔
begin
  induction
  { assume h; refine ⊥ₑ h }
  { assume a L ih h; refine bbeq_cons_refl L a }
end;

opaque symbol bbeq_eq L M : π (size L = size M) → π (istrue (0 < size L)) → π (bbeq L M) → π (L = M) ≔
begin
  induction
  { assume M hs h0 h; refine ⊥ₑ h0 }
  { assume a L ih; induction
    { assume hs h0 h;
      have hs' : π (size L +1 = 0) { refine hs };
      refine ⊥ₑ (s≠0 hs') }
    { assume b M ihM hs h0 h;
      have hs' : π (size L +1 = size M +1) { refine hs };
      refine bbeq_cons_eq L M a b (+1_inj hs') h } }
end;

// (→) equal classes have equal truncations (`cl_inj`); the truncation of a
// digit-list value is the value of its `take n` (`trunc_bits2natB`), which is
// the whole list since |map pb L| = n; then `bits2natB_inj`, `map_pb_inj`,
// and `bbeq` is reflexive. (←) `bbeq_eq` gives L = M.
opaque symbol bb_equal n (L M : 𝕃 o) : π (istrue (0 < n)) → π (size L = n) → π (size M = n) → π ((bbterm n L = bbterm n M) = bbeq L M) ≔
begin
  assume n L M hn hL hM;
  have hsL : π (size (map pb L) = n) { rewrite (size_map pb L); refine hL };
  have hsM : π (size (map pb M) = n) { rewrite (size_map pb M); refine hM };
  have htL : π (take n (map pb L) = map pb L) { rewrite left hsL; refine take_size (map pb L) };
  have htM : π (take n (map pb M) = map pb M) { rewrite left hsM; refine take_size (map pb M) };
  have hL0 : π (istrue (0 < size L)) { rewrite hL; refine hn };
  have hM0 : π (istrue (0 < size M)) { rewrite hM; refine hn };
  have hLM : π (size L = size M) { rewrite hL; rewrite hM; reflexivity };
  apply prop_ext; apply ∧ᵢ
  { assume h;
    have h1 : π (trunc n (bits2natB (map pb L)) = trunc n (bits2natB (map pb M)))
      { refine cl_inj n (bits2natB (map pb L)) (bits2natB (map pb M)) h };
    have h2 : π (bits2natB (map pb L) = bits2natB (map pb M))
      { rewrite left htL; rewrite left htM;
        rewrite left (trunc_bits2natB n (map pb L)); rewrite left (trunc_bits2natB n (map pb M));
        refine h1 };
    have hs : π (size (map pb L) = size (map pb M)) { rewrite hsL; rewrite hsM; reflexivity };
    have h3 : π (L = M) { refine map_pb_inj L M (bits2natB_inj (map pb L) (map pb M) hs h2) };
    rewrite h3; refine bbeq_refl M hM0 }
  { assume h;
    have e : π (L = M) { refine bbeq_eq L M hLM hL0 h };
    rewrite e; reflexivity }
end;

/* ------------------------------------------------------------------------
   Compatibility certificates: every rule on `cl` respects ≈ n
   ------------------------------------------------------------------------ */

/* ------------------------------------------------------------------------
   Group "compatibility certificates of the rules on cl, and their agreement
   with lift/lift2".

   Each `*_compat` has the shape `Stdlib.Quotient.lift2` (resp. `lift`)
   expects for its `hf` argument. The proofs all follow one pattern:
   `apply sound` reduces the class equation to `π (≈ n a b)`, `simplify π`
   displays it as `trunc n a = trunc n b`, and the toolkit lemmas push the
   truncations onto the representatives, where the hypotheses rewrite.
   ------------------------------------------------------------------------ */

opaque symbol bvadd_compat n x x' : π (≈ n x x') → Π y y', π (≈ n y y') →
  π (bvadd (class (≈ n) x) (class (≈ n) y) = bvadd (class (≈ n) x') (class (≈ n) y')) ≔
begin
  assume n x x' hx y y' hy;
  apply sound; simplify π;
  rewrite (trunc_idem n (x + y)); rewrite (trunc_idem n (x' + y'));
  rewrite (trunc_add_lr n x y); rewrite (trunc_add_lr n x' y');
  rewrite hx; rewrite hy; reflexivity
end;

opaque symbol bvmul_compat n x x' : π (≈ n x x') → Π y y', π (≈ n y y') →
  π (bvmul (class (≈ n) x) (class (≈ n) y) = bvmul (class (≈ n) x') (class (≈ n) y')) ≔
begin
  assume n x x' hx y y' hy;
  apply sound; simplify π;
  rewrite (trunc_idem n (x * y)); rewrite (trunc_idem n (x' * y'));
  rewrite (trunc_mul_l n x y); rewrite (trunc_mul_r n (trunc n x) y);
  rewrite (trunc_mul_l n x' y'); rewrite (trunc_mul_r n (trunc n x') y');
  rewrite hx; rewrite hy; reflexivity
end;

opaque symbol bvsub_compat n x x' : π (≈ n x x') → Π y y', π (≈ n y y') →
  π (bvsub (class (≈ n) x) (class (≈ n) y) = bvsub (class (≈ n) x') (class (≈ n) y')) ≔
begin
  assume n x x' hx y y' hy;
  apply sound; simplify π;
  rewrite (trunc_idem n (x + (2 ^ n - trunc n y)));
  rewrite (trunc_idem n (x' + (2 ^ n - trunc n y')));
  rewrite (trunc_add_l n x (2 ^ n - trunc n y));
  rewrite (trunc_add_l n x' (2 ^ n - trunc n y'));
  rewrite hx; rewrite hy; reflexivity
end;

opaque symbol bvand_compat n x x' : π (≈ n x x') → Π y y', π (≈ n y y') →
  π (bvand (class (≈ n) x) (class (≈ n) y) = bvand (class (≈ n) x') (class (≈ n) y')) ≔
begin
  assume n x x' hx y y' hy;
  apply sound; simplify π;
  rewrite left (bitwise_trunc_l (Stdlib.Bool.and) n x y);
  rewrite left (bitwise_trunc_r (Stdlib.Bool.and) n (trunc n x) y);
  rewrite left (bitwise_trunc_l (Stdlib.Bool.and) n x' y');
  rewrite left (bitwise_trunc_r (Stdlib.Bool.and) n (trunc n x') y');
  rewrite hx; rewrite hy; reflexivity
end;

opaque symbol bvor_compat n x x' : π (≈ n x x') → Π y y', π (≈ n y y') →
  π (bvor (class (≈ n) x) (class (≈ n) y) = bvor (class (≈ n) x') (class (≈ n) y')) ≔
begin
  assume n x x' hx y y' hy;
  apply sound; simplify π;
  rewrite left (bitwise_trunc_l (Stdlib.Bool.or) n x y);
  rewrite left (bitwise_trunc_r (Stdlib.Bool.or) n (trunc n x) y);
  rewrite left (bitwise_trunc_l (Stdlib.Bool.or) n x' y');
  rewrite left (bitwise_trunc_r (Stdlib.Bool.or) n (trunc n x') y');
  rewrite hx; rewrite hy; reflexivity
end;

opaque symbol bvxor_compat n x x' : π (≈ n x x') → Π y y', π (≈ n y y') →
  π (bvxor (class (≈ n) x) (class (≈ n) y) = bvxor (class (≈ n) x') (class (≈ n) y')) ≔
begin
  assume n x x' hx y y' hy;
  apply sound; simplify π;
  rewrite left (bitwise_trunc_l (Stdlib.Bool.xorb) n x y);
  rewrite left (bitwise_trunc_r (Stdlib.Bool.xorb) n (trunc n x) y);
  rewrite left (bitwise_trunc_l (Stdlib.Bool.xorb) n x' y');
  rewrite left (bitwise_trunc_r (Stdlib.Bool.xorb) n (trunc n x') y');
  rewrite hx; rewrite hy; reflexivity
end;

opaque symbol concat_compat m n x x' : π (≈ m x x') → Π y y', π (≈ n y y') →
  π (concat (class (≈ m) x) (class (≈ n) y) = concat (class (≈ m) x') (class (≈ n) y')) ≔
begin
  assume m n x x' hx y y' hy;
  apply sound; simplify π;
  rewrite hx; rewrite hy; reflexivity
end;

opaque symbol bvneg_compat n x x' : π (≈ n x x') →
  π (bvneg (class (≈ n) x) = bvneg (class (≈ n) x')) ≔
begin
  assume n x x' hx;
  apply sound; simplify π;
  rewrite hx; reflexivity
end;

opaque symbol bvnot_compat n x x' : π (≈ n x x') →
  π (bvnot (class (≈ n) x) = bvnot (class (≈ n) x')) ≔
begin
  assume n x x' hx;
  apply sound; simplify π;
  rewrite left (bitwise_trunc_l (λ (a _ : 𝔹), Stdlib.Bool.not a) n x x);
  rewrite left (bitwise_trunc_r (λ (a _ : 𝔹), Stdlib.Bool.not a) n (trunc n x) x);
  rewrite left (bitwise_trunc_l (λ (a _ : 𝔹), Stdlib.Bool.not a) n x' x');
  rewrite left (bitwise_trunc_r (λ (a _ : 𝔹), Stdlib.Bool.not a) n (trunc n x') x');
  rewrite hx; reflexivity
end;

opaque symbol extract_compat n i j x x' : π (≈ n x x') →
  π (extract i j (class (≈ n) x) = extract i j (class (≈ n) x')) ≔
begin
  assume n i j x x' hx;
  apply sound; simplify π;
  rewrite hx; reflexivity
end;

opaque symbol zero_extend_compat n k x x' : π (≈ n x x') →
  π (zero_extend k (class (≈ n) x) = zero_extend k (class (≈ n) x')) ≔
begin
  assume n k x x' hx;
  apply sound; simplify π;
  rewrite hx; reflexivity
end;

opaque symbol bit_of_compat n i x x' : π (≈ n x x') →
  π (bit_of i (class (≈ n) x) = bit_of i (class (≈ n) x')) ≔
begin
  assume n i x x' hx;
  change π (istrue (testbit (trunc n x) i) = istrue (testbit (trunc n x') i));
  rewrite hx; reflexivity
end;

/* ---- agreement with Stdlib.Quotient's lift / lift2 ---- */

opaque symbol bvadd_is_lift2 [n] (x y : τ (bitvec n)) :
  π (bvadd x y = @lift2 nat (≈ n) (≈_refl n) (bitvec n) (λ a b, class (≈ n) (trunc n (a + b))) (bvadd_compat n) x y) ≔
begin
  assume n; induction; assume v; induction; assume w; reflexivity
end;

opaque symbol bvmul_is_lift2 [n] (x y : τ (bitvec n)) :
  π (bvmul x y = @lift2 nat (≈ n) (≈_refl n) (bitvec n) (λ a b, class (≈ n) (trunc n (a * b))) (bvmul_compat n) x y) ≔
begin
  assume n; induction; assume v; induction; assume w; reflexivity
end;

opaque symbol bvneg_is_lift [n] (x : τ (bitvec n)) :
  π (bvneg x = @lift nat (≈ n) (bitvec n) (λ a, class (≈ n) (trunc n (2 ^ n - trunc n a))) (bvneg_compat n) x) ≔
begin
  assume n; induction; assume v; reflexivity
end;

/* ------------------------------------------------------------------------
   Closed computation on literals: the literal rules, as equations
   ------------------------------------------------------------------------ */

/* ------------------------------------------------------------------------
   Group "closed computation on literals": the literal rules as equations.
   `bvlit n l ≡ class (≈ n) (bits2natB l)` is still transparent here, so every
   rule on `cl` applies by conversion and each equation between classes is
   `sound` applied to an equation of truncations.
   ------------------------------------------------------------------------ */

// ---- helpers ----

// 0 shifted right stays 0.
opaque symbol lit_shiftr_0 j : π (0 >>> j = 0) ≔
begin
  induction
  { reflexivity }
  { assume j ih; refine feq div2 ih }
end;

// Dropping j digits is shifting the value right by j.
opaque symbol lit_bits2natB_drop l j : π (bits2natB (drop j l) = bits2natB l >>> j) ≔
begin
  have aux : Π j l, π (bits2natB (drop j l) = bits2natB l >>> j)
  { induction
    { assume l; reflexivity }
    { assume j ih; induction
      { change π (0 = div2 (0 >>> j)); rewrite lit_shiftr_0 j; reflexivity }
      { assume b l ihl;
        change π (bits2natB (drop j l) = div2 (((if b 1 0) + 2 * bits2natB l) >>> j));
        rewrite shiftr_div2 j ((if b 1 0) + 2 * bits2natB l);
        rewrite div2_digit b (bits2natB l);
        refine ih l } } };
  assume l j; refine aux j l
end;

// Left shift is multiplication by a power of two.
opaque symbol lit_shiftl_mul x n : π (x <<< n = 2 ^ n * x) ≔
begin
  assume x; induction
  { reflexivity }
  { assume n ih;
    change π (x <<< n + x <<< n = (2 ^ n + 2 ^ n) * x);
    rewrite ih; rewrite mulnDl (2 ^ n) (2 ^ n) x; reflexivity }
end;

// The value of `take k l` already fits in k bits.
opaque symbol lit_trunc_take k l : π (trunc k (bits2natB (take k l)) = bits2natB (take k l)) ≔
begin
  induction
  { assume l; reflexivity }
  { assume k ih; induction
    { refine trunc_0 (k +1) }
    { assume b l ihl;
      change π (trunc (k +1) ((if b 1 0) + 2 * bits2natB (take k l)) = (if b 1 0) + 2 * bits2natB (take k l));
      rewrite trunc_digit k b (bits2natB (take k l)); rewrite ih l; reflexivity } }
end;

// `eqb` decides equality of digits.
opaque symbol lit_eqb_correct x y : π (istrue (eqb x y)) → π (x = y) ≔
begin
  induction
  { induction { assume h; reflexivity } { assume h; refine ⊥ₑ h } }
  { induction { assume h; refine ⊥ₑ h } { assume h; reflexivity } }
end;

opaque symbol lit_eql_eqb_refl l : π (istrue (eql eqb l l)) ≔
begin
  induction
  { refine ⊤ᵢ }
  { assume x l ih; apply ∨ₑ (case_𝔹 x)
    { assume hx; rewrite hx; refine ih }
    { assume hx; rewrite hx; refine ih } }
end;

opaque symbol lit_eql_eqb_correct l m : π (istrue (eql eqb l m)) → π (l = m) ≔
begin
  induction
  { induction
    { assume h; reflexivity }
    { assume y m ihm h; refine ⊥ₑ h } }
  { assume x l ih; induction
    { assume h; refine ⊥ₑ h }
    { assume y m ihm h;
      have h1 : π (x = y) { refine lit_eqb_correct x y (@andₑ₁ (eqb x y) (eql eqb l m) h) };
      have h2 : π (l = m) { refine ih m (@andₑ₂ (eqb x y) (eql eqb l m) h) };
      rewrite h1; rewrite h2; reflexivity } }
end;

// ---- requested lemmas ----

opaque symbol bits2natB_zipbits op n l m : π (bits2natB (zipbits op n l m) = bitwise op n (bits2natB l) (bits2natB m)) ≔
begin
  assume op; induction
  { assume l m; reflexivity }
  { assume n ih; induction
    { induction
      { change π ((if (op false false) 1 0) + 2 * bits2natB (zipbits op n □ □)
                  = (if (op false false) 1 0) + 2 * bitwise op n 0 0);
        rewrite ih □ □; reflexivity }
      { assume b m ihm;
        change π ((if (op false b) 1 0) + 2 * bits2natB (zipbits op n □ m)
                  = (if (op false (odd ((if b 1 0) + 2 * bits2natB m))) 1 0)
                    + 2 * bitwise op n 0 (div2 ((if b 1 0) + 2 * bits2natB m)));
        rewrite odd_digit b (bits2natB m); rewrite div2_digit b (bits2natB m);
        rewrite ih □ m; reflexivity } }
    { assume a l ihl; induction
      { change π ((if (op a false) 1 0) + 2 * bits2natB (zipbits op n l □)
                  = (if (op (odd ((if a 1 0) + 2 * bits2natB l)) false) 1 0)
                    + 2 * bitwise op n (div2 ((if a 1 0) + 2 * bits2natB l)) 0);
        rewrite odd_digit a (bits2natB l); rewrite div2_digit a (bits2natB l);
        rewrite ih l □; reflexivity }
      { assume b m ihm;
        change π ((if (op a b) 1 0) + 2 * bits2natB (zipbits op n l m)
                  = (if (op (odd ((if a 1 0) + 2 * bits2natB l)) (odd ((if b 1 0) + 2 * bits2natB m))) 1 0)
                    + 2 * bitwise op n (div2 ((if a 1 0) + 2 * bits2natB l)) (div2 ((if b 1 0) + 2 * bits2natB m)));
        rewrite odd_digit a (bits2natB l); rewrite odd_digit b (bits2natB m);
        rewrite div2_digit a (bits2natB l); rewrite div2_digit b (bits2natB m);
        rewrite ih l m; reflexivity } } }
end;

opaque symbol bit_of_bvlit n i l : π (bit_of i (bvlit n l) = istrue (nth false (take n l) i)) ≔
begin
  assume n i l;
  change π (istrue (testbit (trunc n (bits2natB l)) i) = istrue (nth false (take n l) i));
  rewrite trunc_bits2natB n l; rewrite testbit_bits2natB (take n l) i; reflexivity
end;

opaque symbol bvand_bvlit n l m : π (bvand (bvlit n l) (bvlit n m) = bvlit n (zipbits (Stdlib.Bool.and) n l m)) ≔
begin
  assume n l m;
  have h : π (trunc n (bitwise (Stdlib.Bool.and) n (bits2natB l) (bits2natB m))
             = trunc n (bits2natB (zipbits (Stdlib.Bool.and) n l m)))
  { rewrite bits2natB_zipbits (Stdlib.Bool.and) n l m; reflexivity };
  refine sound (≈ n) (bitwise (Stdlib.Bool.and) n (bits2natB l) (bits2natB m))
    (bits2natB (zipbits (Stdlib.Bool.and) n l m)) h
end;

opaque symbol bvor_bvlit n l m : π (bvor (bvlit n l) (bvlit n m) = bvlit n (zipbits (Stdlib.Bool.or) n l m)) ≔
begin
  assume n l m;
  have h : π (trunc n (bitwise (Stdlib.Bool.or) n (bits2natB l) (bits2natB m))
             = trunc n (bits2natB (zipbits (Stdlib.Bool.or) n l m)))
  { rewrite bits2natB_zipbits (Stdlib.Bool.or) n l m; reflexivity };
  refine sound (≈ n) (bitwise (Stdlib.Bool.or) n (bits2natB l) (bits2natB m))
    (bits2natB (zipbits (Stdlib.Bool.or) n l m)) h
end;

opaque symbol bvxor_bvlit n l m : π (bvxor (bvlit n l) (bvlit n m) = bvlit n (zipbits (Stdlib.Bool.xorb) n l m)) ≔
begin
  assume n l m;
  have h : π (trunc n (bitwise (Stdlib.Bool.xorb) n (bits2natB l) (bits2natB m))
             = trunc n (bits2natB (zipbits (Stdlib.Bool.xorb) n l m)))
  { rewrite bits2natB_zipbits (Stdlib.Bool.xorb) n l m; reflexivity };
  refine sound (≈ n) (bitwise (Stdlib.Bool.xorb) n (bits2natB l) (bits2natB m))
    (bits2natB (zipbits (Stdlib.Bool.xorb) n l m)) h
end;

opaque symbol bvnot_bvlit n l : π (bvnot (bvlit n l) = bvlit n (zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) n l l)) ≔
begin
  assume n l;
  have h : π (trunc n (bitwise (λ (a _ : 𝔹), Stdlib.Bool.not a) n (bits2natB l) (bits2natB l))
             = trunc n (bits2natB (zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) n l l)))
  { rewrite bits2natB_zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) n l l; reflexivity };
  refine sound (≈ n) (bitwise (λ (a _ : 𝔹), Stdlib.Bool.not a) n (bits2natB l) (bits2natB l))
    (bits2natB (zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) n l l)) h
end;

opaque symbol concat_bvlit m n l l' : π (concat (bvlit m l) (bvlit n l') = bvlit (m + n) (fit n l' ++ take m l)) ≔
begin
  assume m n l l';
  have h : π (trunc (m + n) (trunc n (bits2natB l') + (trunc m (bits2natB l) <<< n))
             = trunc (m + n) (bits2natB (fit n l' ++ take m l)))
  { rewrite bits2natB_cat (fit n l') (take m l);
    rewrite bits2natB_fit n l';
    rewrite size_fit n l';
    rewrite left (trunc_bits2natB m l);
    rewrite lit_shiftl_mul (trunc m (bits2natB l)) n;
    reflexivity };
  have h' : π (≈ (m + n) (trunc n (bits2natB l') + (trunc m (bits2natB l) <<< n))
                 (bits2natB (fit n l' ++ take m l))) { refine h };
  refine @sound nat (≈ (m + n)) (trunc n (bits2natB l') + (trunc m (bits2natB l) <<< n))
    (bits2natB (fit n l' ++ take m l)) h'
end;

opaque symbol extract_bvlit n i j l : π (extract i j (bvlit n l) = bvlit (i - j + 1) (take (i - j + 1) (drop j (take n l)))) ≔
begin
  assume n i j l;
  have h : π (trunc (i - j + 1) (trunc (i - j + 1) (trunc n (bits2natB l) >>> j))
             = trunc (i - j + 1) (bits2natB (take (i - j + 1) (drop j (take n l)))))
  { rewrite trunc_idem (i - j + 1) (trunc n (bits2natB l) >>> j);
    rewrite trunc_bits2natB n l;
    rewrite left (lit_bits2natB_drop (take n l) j);
    rewrite lit_trunc_take (i - j + 1) (drop j (take n l));
    rewrite trunc_bits2natB (i - j + 1) (drop j (take n l));
    reflexivity };
  have h' : π (≈ (i - j + 1) (trunc (i - j + 1) (trunc n (bits2natB l) >>> j))
                 (bits2natB (take (i - j + 1) (drop j (take n l))))) { refine h };
  refine @sound nat (≈ (i - j + 1)) (trunc (i - j + 1) (trunc n (bits2natB l) >>> j))
    (bits2natB (take (i - j + 1) (drop j (take n l)))) h'
end;

opaque symbol zero_extend_bvlit n k l : π (zero_extend k (bvlit n l) = bvlit (k + n) (fit n l)) ≔
begin
  assume n k l;
  have h : π (trunc (k + n) (trunc n (bits2natB l)) = trunc (k + n) (bits2natB (fit n l)))
  { rewrite bits2natB_fit n l; reflexivity };
  have h' : π (≈ (k + n) (trunc n (bits2natB l)) (bits2natB (fit n l))) { refine h };
  refine @sound nat (≈ (k + n)) (trunc n (bits2natB l)) (bits2natB (fit n l)) h'
end;

// The canonical form has exactly k + n digits: pad with k zero digits.
opaque symbol zero_extend_bvlit_pad n k l :
  π (zero_extend k (bvlit n l) = bvlit (k + n) (fit n l ++ nseq k false)) ≔
begin
  assume n k l; apply sound; simplify π;
  rewrite (bits2natB_cat (fit n l) (nseq k false));
  rewrite (bits2natB_nseq_false k);
  rewrite (bits2natB_fit n l);
  reflexivity
end;

opaque symbol bvlit_eq_decide n l m : π ((bvlit n l = bvlit n m) = istrue (eql eqb (fit n l) (fit n m))) ≔
begin
  assume n l m;
  apply propExt (bvlit n l = bvlit n m) (istrue (eql eqb (fit n l) (fit n m)))
  { assume h;
    have ht : π (trunc n (bits2natB l) = trunc n (bits2natB m))
      { refine cl_inj n (bits2natB l) (bits2natB m) h };
    have hb : π (bits2natB (fit n l) = bits2natB (fit n m))
      { rewrite bits2natB_fit n l; rewrite bits2natB_fit n m; refine ht };
    have hs : π (size (fit n l) = size (fit n m))
      { rewrite size_fit n l; rewrite size_fit n m; reflexivity };
    have hf : π (fit n l = fit n m) { refine bits2natB_inj (fit n l) (fit n m) hs hb };
    rewrite hf; refine lit_eql_eqb_refl (fit n m) }
  { assume h;
    have hf : π (fit n l = fit n m) { refine lit_eql_eqb_correct (fit n l) (fit n m) h };
    have ht : π (trunc n (bits2natB l) = trunc n (bits2natB m))
      { rewrite left (bits2natB_fit n l); rewrite left (bits2natB_fit n m); rewrite hf; reflexivity };
    have ht' : π (≈ n (bits2natB l) (bits2natB m)) { refine ht };
    refine @sound nat (≈ n) (bits2natB l) (bits2natB m) ht' }
end;

/* ------------------------------------------------------------------------
   The digit-list adder and cvc5's ripple-carry adder
   ------------------------------------------------------------------------ */

/* Group "the digit-list adder and cvc5's ripple-carry adder". */

// sanity: the digit form of a sum with carry, a and b and c all fixed
assert ⊢ bits2natB (adc (true ⸬ □) (true ⸬ □) true) ≡ 3;

/* ---------------- helpers ---------------- */

// The full adder on digits: sum digit plus twice the carry is the sum of the
// three input digits. Eight Boolean cases, each a closed computation.
opaque symbol adder_full (a b c : 𝔹) :
  π ((if ((a xorb b) xorb c) 1 0)
     + 2 * (if ((Stdlib.Bool.or) ((Stdlib.Bool.and) a b) ((Stdlib.Bool.and) (a xorb b) c)) 1 0)
     = (if a 1 0) + (if b 1 0) + (if c 1 0)) ≔
begin
  assume a b c;
  apply ∨ₑ (case_𝔹 a)
  { assume ha; rewrite ha; apply ∨ₑ (case_𝔹 b)
    { assume hb; rewrite hb; apply ∨ₑ (case_𝔹 c)
      { assume hc; rewrite hc; reflexivity }
      { assume hc; rewrite hc; reflexivity } }
    { assume hb; rewrite hb; apply ∨ₑ (case_𝔹 c)
      { assume hc; rewrite hc; reflexivity }
      { assume hc; rewrite hc; reflexivity } } }
  { assume ha; rewrite ha; apply ∨ₑ (case_𝔹 b)
    { assume hb; rewrite hb; apply ∨ₑ (case_𝔹 c)
      { assume hc; rewrite hc; reflexivity }
      { assume hc; rewrite hc; reflexivity } }
    { assume hb; rewrite hb; apply ∨ₑ (case_𝔹 c)
      { assume hc; rewrite hc; reflexivity }
      { assume hc; rewrite hc; reflexivity } } }
end;

// The half adder (the missing-digit cases of `adc`).
opaque symbol adder_half (b c : 𝔹) :
  π ((if (b xorb c) 1 0) + 2 * (if ((Stdlib.Bool.and) b c) 1 0) = (if b 1 0) + (if c 1 0)) ≔
begin
  assume b c;
  apply ∨ₑ (case_𝔹 b)
  { assume hb; rewrite hb; apply ∨ₑ (case_𝔹 c)
    { assume hc; rewrite hc; reflexivity }
    { assume hc; rewrite hc; reflexivity } }
  { assume hb; rewrite hb; apply ∨ₑ (case_𝔹 c)
    { assume hc; rewrite hc; reflexivity }
    { assume hc; rewrite hc; reflexivity } }
end;

// The arithmetic of one adder step: if the digit identity d + 2d' = a + b + c
// holds, then d + 2 (L + M + d') = (a + 2L) + (b + 2M) + c. Double induction
// on L and M: each step is the hypothesis under `+1 +1` by conversion.
opaque symbol adder_step (d d' a b c L M X : ℕ) :
  π (X = L + M + d') → π (d + 2 * d' = a + b + c) →
  π (d + 2 * X = a + 2 * L + (b + 2 * M) + c) ≔
begin
  assume d d' a b c L M X hX h;
  have aux : Π L' M', π (d + 2 * (L' + M' + d') = a + 2 * L' + (b + 2 * M') + c)
  { induction
    { induction
      { refine h }
      { assume M' ih; refine feq (λ z, z +1 +1) ih } }
    { assume L' ih M'; refine feq (λ z, z +1 +1) (ih M') } };
  rewrite hX; refine aux L M
end;

/* ---------------- requested lemmas ---------------- */

opaque symbol bits2natB_adc l m c : π (bits2natB (adc l m c) = bits2natB l + bits2natB m + (if c 1 0)) ≔
begin
  induction
  { induction
    { assume c; reflexivity }
    { assume b m ih c;
      refine adder_step (if (b xorb c) 1 0) (if ((Stdlib.Bool.and) b c) 1 0)
        0 (if b 1 0) (if c 1 0) 0 (bits2natB m)
        (bits2natB (adc □ m ((Stdlib.Bool.and) b c)))
        (ih ((Stdlib.Bool.and) b c)) (adder_half b c) } }
  { assume a l ih; induction
    { assume c;
      refine adder_step (if (a xorb c) 1 0) (if ((Stdlib.Bool.and) a c) 1 0)
        (if a 1 0) 0 (if c 1 0) (bits2natB l) 0
        (bits2natB (adc l □ ((Stdlib.Bool.and) a c)))
        (ih □ ((Stdlib.Bool.and) a c)) (adder_half a c) }
    { assume b m ihm c;
      refine adder_step (if ((a xorb b) xorb c) 1 0)
        (if ((Stdlib.Bool.or) ((Stdlib.Bool.and) a b) ((Stdlib.Bool.and) (a xorb b) c)) 1 0)
        (if a 1 0) (if b 1 0) (if c 1 0) (bits2natB l) (bits2natB m)
        (bits2natB (adc l m ((Stdlib.Bool.or) ((Stdlib.Bool.and) a b) ((Stdlib.Bool.and) (a xorb b) c))))
        (ih m ((Stdlib.Bool.or) ((Stdlib.Bool.and) a b) ((Stdlib.Bool.and) (a xorb b) c)))
        (adder_full a b c) } }
end;

opaque symbol bvadd_bvlit n l m : π (bvadd (bvlit n l) (bvlit n m) = bvlit n (take n (adc l m false))) ≔
begin
  assume n l m; apply sound; simplify π;
  rewrite trunc_idem n (bits2natB l + bits2natB m);
  rewrite left (trunc_bits2natB n (adc l m false));
  rewrite trunc_idem n (bits2natB (adc l m false));
  rewrite bits2natB_adc l m false;
  reflexivity
end;

// cvc5's ripple-carry adder on propositions is the digit-list adder read
// through `pb`, for every carry-in; `take (size L)` drops the carry-out.
// Induction on L with M and the carry general; the size hypothesis kills the
// mixed cases, for which `rca` has no rule.
opaque symbol adder_rca_adc_c L M c : π (size L = size M) →
  π (map pb (rca L M c) = take (size L) (adc (map pb L) (map pb M) (pb c))) ≔
begin
  induction
  { induction
    { assume c hs; reflexivity }
    { assume b M ih c hs; refine ⊥ₑ (0≠s [size M] hs) } }
  { assume a L ih; induction
    { assume c hs; refine ⊥ₑ (s≠0 [size L] hs) }
    { assume b M ihm c hs;
      have hs' : π (size L = size M) { refine +1_inj hs };
      change π (pb (xor (xor a b) c) ⸬ map pb (rca L M ((a ∧ b) ∨ ((xor a b) ∧ c)))
               = (((pb a) xorb (pb b)) xorb (pb c))
                 ⸬ take (size L) (adc (map pb L) (map pb M)
                     ((Stdlib.Bool.or) ((Stdlib.Bool.and) (pb a) (pb b))
                                       ((Stdlib.Bool.and) ((pb a) xorb (pb b)) (pb c)))));
      rewrite ih M ((a ∧ b) ∨ ((xor a b) ∧ c)) hs';
      rewrite pb_or (a ∧ b) ((xor a b) ∧ c);
      rewrite pb_and a b; rewrite pb_and (xor a b) c;
      rewrite pb_xor (xor a b) c; rewrite pb_xor a b;
      reflexivity } }
end;

opaque symbol rca_adc L M : π (size L = size M) → π (map pb (rca L M ⊥) = take (size L) (adc (map pb L) (map pb M) false)) ≔
begin
  assume L M hs; refine adder_rca_adc_c L M ⊥ hs
end;

opaque symbol bb_add n L M : π (size L = n) → π (size M = n) → π (bvadd (bbterm n L) (bbterm n M) = bbterm n (rca L M ⊥)) ≔
begin
  assume n L M hL hM;
  have hs : π (size L = size M) { rewrite hL; rewrite hM; reflexivity };
  have e : π (map pb (rca L M ⊥) = take n (adc (map pb L) (map pb M) false))
    { rewrite left hL; refine rca_adc L M hs };
  change π (bvadd (bvlit n (map pb L)) (bvlit n (map pb M)) = bvlit n (map pb (rca L M ⊥)));
  rewrite bvadd_bvlit n (map pb L) (map pb M);
  rewrite e; reflexivity
end;

/* ---------------- the complement identity ---------------- */

// A digit and its complement add up to 1.
opaque symbol adder_not_digit (b : 𝔹) : π ((if (Stdlib.Bool.not b) 1 0) + (if b 1 0) = 1) ≔
begin
  assume b; apply ∨ₑ (case_𝔹 b)
  { assume hb; rewrite hb; reflexivity }
  { assume hb; rewrite hb; reflexivity }
end;

// The arithmetic of one complement step: if d + e = 1 and B + T + 1 = P then
// (d + 2B) + (e + 2T) + 1 = 2P. Double induction on B and T, each step is the
// hypothesis under `+1 +1` by conversion.
opaque symbol adder_compl_step (d e B T P : ℕ) :
  π (d + e = 1) → π (B + T + 1 = P) → π (d + 2 * B + (e + 2 * T) + 1 = 2 * P) ≔
begin
  assume d e B T P h hP; rewrite left hP;
  have aux : Π B' T', π (d + 2 * B' + (e + 2 * T') + 1 = 2 * (B' + T' + 1))
  { induction
    { induction
      { refine feq (λ z, z +1) h }
      { assume T' ih; refine feq (λ z, z +1 +1) ih } }
    { assume B' ih T'; refine feq (λ z, z +1 +1) (ih T') } };
  refine aux B T
end;

// The bitwise complement of the low n bits of x, plus those bits, plus 1, is 2ⁿ.
opaque symbol bitwise_not_add n x :
  π (bitwise (λ (a _ : 𝔹), Stdlib.Bool.not a) n x x + trunc n x + 1 = 2 ^ n) ≔
begin
  induction
  { assume x; reflexivity }
  { assume n ih x;
    refine adder_compl_step (if (Stdlib.Bool.not (odd x)) 1 0) (if (odd x) 1 0)
      (bitwise (λ (a _ : 𝔹), Stdlib.Bool.not a) n (div2 x) (div2 x)) (trunc n (div2 x)) (2 ^ n)
      (adder_not_digit (odd x)) (ih (div2 x)) }
end;

// Hence 2ⁿ - trunc n x is the complement plus one, exactly (no truncation needed).
opaque symbol adder_compl_sub n x :
  π (2 ^ n - trunc n x = bitwise (λ (a _ : 𝔹), Stdlib.Bool.not a) n x x + 1) ≔
begin
  assume n x;
  rewrite left (bitwise_not_add n x);
  refine addnK (bitwise (λ (a _ : 𝔹), Stdlib.Bool.not a) n x x + 1) (trunc n x)
end;

/* ---------------- zipbits is bitwise on values ---------------- */

// One step of `bitwise` on two digit forms.
opaque symbol adder_zip_step op n a b x y Z : π (Z = bitwise op n x y) →
  π ((if (op a b) 1 0) + 2 * Z = bitwise op (n +1) ((if a 1 0) + 2 * x) ((if b 1 0) + 2 * y)) ≔
begin
  assume op n a b x y Z hZ; rewrite hZ;
  change π ((if (op a b) 1 0) + 2 * bitwise op n x y
            = (if (op (odd ((if a 1 0) + 2 * x)) (odd ((if b 1 0) + 2 * y))) 1 0)
              + 2 * bitwise op n (div2 ((if a 1 0) + 2 * x)) (div2 ((if b 1 0) + 2 * y)));
  rewrite odd_digit a x; rewrite odd_digit b y;
  rewrite div2_digit a x; rewrite div2_digit b y;
  reflexivity
end;

// The value of `zipbits op n l m` is `bitwise op n` of the values (a missing
// digit reads false, i.e. the value 0 reads as the digit form 0 + 2 * 0).
opaque symbol adder_bits2natB_zipbits op n l m :
  π (bits2natB (zipbits op n l m) = bitwise op n (bits2natB l) (bits2natB m)) ≔
begin
  assume op; induction
  { assume l m; reflexivity }
  { assume n ih; induction
    { induction
      { refine adder_zip_step op n false false 0 0 (bits2natB (zipbits op n □ □)) (ih □ □) }
      { assume b m ihm;
        refine adder_zip_step op n false b 0 (bits2natB m) (bits2natB (zipbits op n □ m)) (ih □ m) } }
    { assume a l ihl; induction
      { refine adder_zip_step op n a false (bits2natB l) 0 (bits2natB (zipbits op n l □)) (ih l □) }
      { assume b m ihm;
        refine adder_zip_step op n a b (bits2natB l) (bits2natB m) (bits2natB (zipbits op n l m)) (ih l m) } } }
end;

/* ---------------- requested lemmas ---------------- */

opaque symbol bvneg_bvlit n l : π (bvneg (bvlit n l) = bvlit n (take n (adc (zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) n l l) □ true))) ≔
begin
  assume n l; apply sound; simplify π;
  rewrite trunc_idem n (2 ^ n - trunc n (bits2natB l));
  rewrite left (trunc_bits2natB n (adc (zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) n l l) □ true));
  rewrite trunc_idem n (bits2natB (adc (zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) n l l) □ true));
  rewrite bits2natB_adc (zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) n l l) □ true;
  rewrite adder_bits2natB_zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) n l l;
  rewrite adder_compl_sub n (bits2natB l);
  reflexivity
end;

opaque symbol bvsub_bvlit n l m : π (bvsub (bvlit n l) (bvlit n m) = bvlit n (take n (adc l (zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) n m m) true))) ≔
begin
  assume n l m; apply sound; simplify π;
  rewrite trunc_idem n (bits2natB l + (2 ^ n - trunc n (bits2natB m)));
  rewrite left (trunc_bits2natB n (adc l (zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) n m m) true));
  rewrite trunc_idem n (bits2natB (adc l (zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) n m m) true));
  rewrite bits2natB_adc l (zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) n m m) true;
  rewrite adder_bits2natB_zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) n m m;
  rewrite adder_compl_sub n (bits2natB m);
  reflexivity
end;

/* ------------------------------------------------------------------------
   Bits of the structural and bitwise operators
   ------------------------------------------------------------------------ */

/* ------------------------------------------------------------------------
   Group "bits of the structural and bitwise operators".
   Helpers are prefixed `bits_`.
   ------------------------------------------------------------------------ */

// ---- helpers ----

// A failed Boolean `<` is a `≤` the other way round.
opaque symbol bits_not_lt b n : π ((b < n) = false) → π (istrue (n ≤ b)) ≔
begin
  assume b n h;
  apply ∨ₑ (leq_total n b)
  { assume h1; refine h1 }
  { assume h1;
    apply ∨ₑ (∧ₑ₁ (leq_eqVlt b n) h1)
    { assume e; rewrite e; refine ≤_refl n }
    { assume hlt; refine ⊥ₑ (=⇒ (feq istrue h) hlt) } }
end;

// Boolean connectives read as propositions.
opaque symbol bits_istrue_and (p q : 𝔹) : π (istrue ((Stdlib.Bool.and) p q) = (istrue p ∧ istrue q)) ≔
begin
  assume p q;
  refine propExt (istrue ((Stdlib.Bool.and) p q)) (istrue p ∧ istrue q) (@∧_istrue p q) (@istrue_and p q)
end;

opaque symbol bits_istrue_or (p q : 𝔹) : π (istrue ((Stdlib.Bool.or) p q) = (istrue p ∨ istrue q)) ≔
begin
  assume p q;
  refine propExt (istrue ((Stdlib.Bool.or) p q)) (istrue p ∨ istrue q) (@∨_istrue p q) (@istrue_or p q)
end;

opaque symbol bits_istrue_not (p : 𝔹) : π (istrue (Stdlib.Bool.not p) = ¬ (istrue p)) ≔
begin
  assume p; apply ∨ₑ (case_𝔹 p)
  { assume h; rewrite h; symmetry; refine ¬⊤ }
  { assume h; rewrite h; symmetry; refine ¬⊥ }
end;

// `xorb` is the propositional `xor` of alethe.prop, through `pb`.
opaque symbol bits_istrue_xorb (p q : 𝔹) : π (istrue (p xorb q) = xor (istrue p) (istrue q)) ≔
begin
  assume p q;
  rewrite left (istrue_pb (xor (istrue p) (istrue q)));
  rewrite pb_xor (istrue p) (istrue q);
  rewrite pb_istrue p; rewrite pb_istrue q; reflexivity
end;

// `istrue` commutes with `if`.
opaque symbol bits_istrue_if (c x y : 𝔹) : π (istrue (if c x y) = if c (istrue x) (istrue y)) ≔
begin
  assume c x y; apply ∨ₑ (case_𝔹 c)
  { assume h; rewrite h; reflexivity }
  { assume h; rewrite h; reflexivity }
end;

// Bits of `a + b <<< n` when a fits in n bits: the low n bits are a's, the
// others are b's shifted. Induction on n, general in a and m; the step is
// `div2 (a + 2 * s) = div2 a + s` under `testbit _ m`.
opaque symbol bits_testbit_add_shiftl_aux n : Π a b m, π (istrue (a < 2 ^ n)) →
  π (testbit (a + b <<< n) m = if (m < n) (testbit a m) (testbit b (m - n))) ≔
begin
  induction
  { assume a b m h;
    have ha : π (a = 0) { refine ≤0 a h };
    rewrite ha; rewrite subn0 m; reflexivity }
  { assume n ih a b; induction
    { assume h; refine odd_add_double a (b <<< n) }
    { assume m ihm h;
      refine ind_eq (div2_add_double a (b <<< n))
        (λ z, testbit z m = if (m < n) (testbit (div2 a) m) (testbit b (m - n)))
        (ih (div2 a) b m (lt_pow2_div2 n a h)) } }
end;

opaque symbol bits_testbit_add_shiftl a b n m : π (istrue (a < 2 ^ n)) →
  π (testbit (a + b <<< n) m = if (m < n) (testbit a m) (testbit b (m - n))) ≔
begin
  assume a b n m h; refine bits_testbit_add_shiftl_aux n a b m h
end;

// ---- requested lemmas ----

opaque symbol bit_of_ge n (x : τ (bitvec n)) b : π (istrue (n ≤ b)) → π (bit_of b x = ⊥) ≔
begin
  assume n; induction; assume v b h;
  change π (istrue (testbit (trunc n v) b) = ⊥);
  rewrite testbit_trunc_ge n v b h; reflexivity
end;

opaque symbol bit_of_zero_extend n k (x : τ (bitvec n)) b : π (bit_of b (zero_extend k x) = bit_of b x) ≔
begin
  assume n k; induction; assume v b;
  change π (istrue (testbit (trunc (k + n) (trunc n v)) b) = istrue (testbit (trunc n v) b));
  apply ∨ₑ (case_𝔹 (b < k + n))
  { assume h; rewrite testbit_trunc_lt (k + n) (trunc n v) b (true=istrue h); reflexivity }
  { assume h;
    have h1 : π (istrue (k + n ≤ b)) { refine bits_not_lt b (k + n) h };
    have h2 : π (istrue (n ≤ b)) { refine @leq_trans n (k + n) b (leq_addl k n) h1 };
    rewrite testbit_trunc_ge (k + n) (trunc n v) b h1;
    rewrite testbit_trunc_ge n v b h2; reflexivity }
end;

opaque symbol bit_of_bvand n (x y : τ (bitvec n)) b : π (bit_of b (bvand x y) = (bit_of b x ∧ bit_of b y)) ≔
begin
  assume n; induction; assume u; induction; assume v b;
  change π (istrue (testbit (trunc n (bitwise (Stdlib.Bool.and) n u v)) b)
            = (istrue (testbit (trunc n u) b) ∧ istrue (testbit (trunc n v) b)));
  rewrite trunc_bitwise (Stdlib.Bool.and) n u v;
  apply ∨ₑ (case_𝔹 (b < n))
  { assume h;
    rewrite testbit_bitwise_lt' (Stdlib.Bool.and) n b u v (true=istrue h);
    rewrite testbit_trunc_lt n u b (true=istrue h);
    rewrite testbit_trunc_lt n v b (true=istrue h);
    refine bits_istrue_and (testbit u b) (testbit v b) }
  { assume h;
    have h1 : π (istrue (n ≤ b)) { refine bits_not_lt b n h };
    rewrite testbit_bitwise_ge' (Stdlib.Bool.and) n b u v h1;
    rewrite testbit_trunc_ge n u b h1;
    rewrite testbit_trunc_ge n v b h1;
    refine bits_istrue_and false false }
end;

opaque symbol bit_of_bvor n (x y : τ (bitvec n)) b : π (bit_of b (bvor x y) = (bit_of b x ∨ bit_of b y)) ≔
begin
  assume n; induction; assume u; induction; assume v b;
  change π (istrue (testbit (trunc n (bitwise (Stdlib.Bool.or) n u v)) b)
            = (istrue (testbit (trunc n u) b) ∨ istrue (testbit (trunc n v) b)));
  rewrite trunc_bitwise (Stdlib.Bool.or) n u v;
  apply ∨ₑ (case_𝔹 (b < n))
  { assume h;
    rewrite testbit_bitwise_lt' (Stdlib.Bool.or) n b u v (true=istrue h);
    rewrite testbit_trunc_lt n u b (true=istrue h);
    rewrite testbit_trunc_lt n v b (true=istrue h);
    refine bits_istrue_or (testbit u b) (testbit v b) }
  { assume h;
    have h1 : π (istrue (n ≤ b)) { refine bits_not_lt b n h };
    rewrite testbit_bitwise_ge' (Stdlib.Bool.or) n b u v h1;
    rewrite testbit_trunc_ge n u b h1;
    rewrite testbit_trunc_ge n v b h1;
    refine bits_istrue_or false false }
end;

opaque symbol bit_of_bvxor n (x y : τ (bitvec n)) b : π (bit_of b (bvxor x y) = xor (bit_of b x) (bit_of b y)) ≔
begin
  assume n; induction; assume u; induction; assume v b;
  change π (istrue (testbit (trunc n (bitwise (Stdlib.Bool.xorb) n u v)) b)
            = xor (istrue (testbit (trunc n u) b)) (istrue (testbit (trunc n v) b)));
  rewrite trunc_bitwise (Stdlib.Bool.xorb) n u v;
  apply ∨ₑ (case_𝔹 (b < n))
  { assume h;
    rewrite testbit_bitwise_lt' (Stdlib.Bool.xorb) n b u v (true=istrue h);
    rewrite testbit_trunc_lt n u b (true=istrue h);
    rewrite testbit_trunc_lt n v b (true=istrue h);
    refine bits_istrue_xorb (testbit u b) (testbit v b) }
  { assume h;
    have h1 : π (istrue (n ≤ b)) { refine bits_not_lt b n h };
    rewrite testbit_bitwise_ge' (Stdlib.Bool.xorb) n b u v h1;
    rewrite testbit_trunc_ge n u b h1;
    rewrite testbit_trunc_ge n v b h1;
    refine bits_istrue_xorb false false }
end;

opaque symbol bit_of_bvnot n (x : τ (bitvec n)) b : π (bit_of b (bvnot x) = (istrue (b < n) ∧ ¬ (bit_of b x))) ≔
begin
  assume n; induction; assume u b;
  change π (istrue (testbit (trunc n (bitwise (λ (a _ : 𝔹), Stdlib.Bool.not a) n u u)) b)
            = (istrue (b < n) ∧ ¬ (istrue (testbit (trunc n u) b))));
  rewrite trunc_bitwise (λ (a _ : 𝔹), Stdlib.Bool.not a) n u u;
  apply ∨ₑ (case_𝔹 (b < n))
  { assume h;
    have e : π (testbit (bitwise (λ (a _ : 𝔹), Stdlib.Bool.not a) n u u) b = Stdlib.Bool.not (testbit u b))
      { refine testbit_bitwise_lt' (λ (a _ : 𝔹), Stdlib.Bool.not a) n b u u (true=istrue h) };
    rewrite e; rewrite h;
    rewrite testbit_trunc_lt n u b (true=istrue h);
    rewrite bits_istrue_not (testbit u b);
    symmetry; refine ⊤∧ (¬ (istrue (testbit u b))) }
  { assume h;
    have h1 : π (istrue (n ≤ b)) { refine bits_not_lt b n h };
    rewrite testbit_bitwise_ge' (λ (a _ : 𝔹), Stdlib.Bool.not a) n b u u h1;
    rewrite h;
    symmetry; refine ⊥∧ (¬ (istrue (testbit (trunc n u) b))) }
end;

opaque symbol bit_of_extract n i j (x : τ (bitvec n)) b : π (bit_of b (extract i j x) = if (b < i - j + 1) (bit_of (j + b) x) ⊥) ≔
begin
  assume n i j; induction; assume v b;
  change π (istrue (testbit (trunc (i - j + 1) (trunc (i - j + 1) (trunc n v >>> j))) b)
            = if (b < i - j + 1) (istrue (testbit (trunc n v) (j + b))) ⊥);
  rewrite trunc_idem (i - j + 1) (trunc n v >>> j);
  apply ∨ₑ (case_𝔹 (b < i - j + 1))
  { assume h; rewrite h;
    rewrite testbit_trunc_lt (i - j + 1) (trunc n v >>> j) b (true=istrue h);
    rewrite shiftr_spec (trunc n v) j b;
    rewrite addnC b j; reflexivity }
  { assume h; rewrite h;
    rewrite testbit_trunc_ge (i - j + 1) (trunc n v >>> j) b (bits_not_lt b (i - j + 1) h);
    reflexivity }
end;

opaque symbol bit_of_concat m n (x : τ (bitvec m)) (y : τ (bitvec n)) b : π (bit_of b (concat x y) = if (b < n) (bit_of b y) (bit_of (b - n) x)) ≔
begin
  assume m n; induction; assume u; induction; assume v b;
  change π (istrue (testbit (trunc (m + n) (trunc n v + (trunc m u <<< n))) b)
            = if (b < n) (istrue (testbit (trunc n v) b)) (istrue (testbit (trunc m u) (b - n))));
  apply ∨ₑ (case_𝔹 (b < m + n))
  { assume h;
    rewrite testbit_trunc_lt (m + n) (trunc n v + (trunc m u <<< n)) b (true=istrue h);
    rewrite bits_testbit_add_shiftl (trunc n v) (trunc m u) n b (trunc_lt n v);
    refine bits_istrue_if (b < n) (testbit (trunc n v) b) (testbit (trunc m u) (b - n)) }
  { assume h;
    have h1 : π (istrue (m + n ≤ b)) { refine bits_not_lt b (m + n) h };
    have h2 : π (istrue (n ≤ b)) { refine @leq_trans n (m + n) b (leq_addl m n) h1 };
    have h3 : π (istrue (m ≤ b - n))
      { rewrite left (addnK m n); refine leq_sub2r (m + n) b n h1 };
    rewrite testbit_trunc_ge (m + n) (trunc n v + (trunc m u <<< n)) b h1;
    rewrite testbit_trunc_ge n v b h2;
    rewrite testbit_trunc_ge m u (b - n) h3;
    symmetry; refine if_same (b < n) ⊥ }
end;

/* ------------------------------------------------------------------------
   Zero literals and the body of bv-zero-extend-eliminate
   ------------------------------------------------------------------------ */

/* ------------------------------------------------------------------------
   Group "rare": the first RARE lemma (zero_extend_concat_zero) and small
   facts about the zero literal `bvlit n (nseq n false)`.
   ------------------------------------------------------------------------ */

// ---- helpers ----

// Shifting zero to the left stays zero: `0 <<< (n +1) ≡ double (0 <<< n)`.
opaque symbol rare_shiftl_0 n : π (0 <<< n = 0) ≔
begin
  induction
  { reflexivity }
  { assume n ih; simplify; rewrite ih; reflexivity }
end;

// Bitwise `and` with zero on the right is zero, for any fuel n:
// `odd 0 ≡ false`, `div2 0 ≡ 0`, and `b and false = false`.
opaque symbol rare_bitwise_and_0_r n v : π (bitwise (Stdlib.Bool.and) n v 0 = 0) ≔
begin
  induction
  { assume v; reflexivity }
  { assume n ih v;
    change π ((if ((Stdlib.Bool.and) (odd v) false) 1 0)
              + 2 * bitwise (Stdlib.Bool.and) n (div2 v) 0 = 0);
    rewrite and_false (odd v); rewrite ih (div2 v); reflexivity }
end;

// Bitwise `and` with zero on the left is zero, for any fuel n:
// `false and b ↪ false` by the defining rule of `and`.
opaque symbol rare_bitwise_and_0_l n v : π (bitwise (Stdlib.Bool.and) n 0 v = 0) ≔
begin
  induction
  { assume v; reflexivity }
  { assume n ih v;
    change π (2 * bitwise (Stdlib.Bool.and) n 0 (div2 v) = 0);
    rewrite ih (div2 v); reflexivity }
end;

// ---- requested lemmas ----

// RARE zero_extend_concat_zero: zero_extend k x = concat #b0…0 x.
// On a representative v both sides are classes of `≈ (k + n)`:
// `trunc n v` and `trunc n v + (trunc k (bits2natB (nseq k false)) <<< n)`;
// the shifted summand is `trunc k 0 <<< n ≡ 0 <<< n = 0`.
opaque symbol zero_extend_concat_zero [n] k (x : τ (bitvec n)) : π (zero_extend k x = concat (bvlit k (nseq k false)) x) ≔
begin
  assume n k; induction; assume v; apply sound; simplify π;
  rewrite bits2natB_nseq_false k; rewrite trunc_0 k; rewrite rare_shiftl_0 n;
  reflexivity
end;

// The zero literal is the class of 0.
opaque symbol bvlit_zero n : π (bvlit n (nseq n false) = class (≈ n) 0) ≔
begin
  assume n; refine feq (class (≈ n)) (bits2natB_nseq_false n)
end;

// x & 0 = 0, through `bitwise and n v 0 = 0`.
opaque symbol bvand_zero_r [n] (x : τ (bitvec n)) : π (bvand x (bvlit n (nseq n false)) = bvlit n (nseq n false)) ≔
begin
  assume n; induction; assume v; apply sound; simplify π;
  rewrite bits2natB_nseq_false n; rewrite rare_bitwise_and_0_r n v; reflexivity
end;

// 0 & x = 0, through `bitwise and n 0 v = 0`.
opaque symbol bvand_zero_l [n] (x : τ (bitvec n)) : π (bvand (bvlit n (nseq n false)) x = bvlit n (nseq n false)) ≔
begin
  assume n; induction; assume v; apply sound; simplify π;
  rewrite bits2natB_nseq_false n; rewrite rare_bitwise_and_0_l n v; reflexivity
end;

/* ------------------------------------------------------------------------
   Literals become rigid. From here on `bvlit n l` never unfolds: comparing two
   literals compares their digit lists, so a 32-bit constant costs 32 steps
   instead of a unary normalisation that can never finish. `bvlit_def` is the
   only way back to the representative. The rules below are the equations
   proved above, installed as rewrite rules (the Stdlib.ExtraRules discipline).
   ------------------------------------------------------------------------ */

opaque bvlit;

rule @bit_of $n $i (bvlit _ $l) ↪ istrue (nth false (take $n $l) $i);
rule @bvadd $n (bvlit _ $l) (bvlit _ $m) ↪ bvlit $n (take $n (adc $l $m false));
rule @bvneg $n (bvlit _ $l) ↪ bvlit $n (take $n (adc (zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) $n $l $l) □ true));
rule @bvsub $n (bvlit _ $l) (bvlit _ $m) ↪ bvlit $n (take $n (adc $l (zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) $n $m $m) true));
rule @bvand $n (bvlit _ $l) (bvlit _ $m) ↪ bvlit $n (zipbits (Stdlib.Bool.and) $n $l $m);
rule @bvor $n (bvlit _ $l) (bvlit _ $m) ↪ bvlit $n (zipbits (Stdlib.Bool.or) $n $l $m);
rule @bvxor $n (bvlit _ $l) (bvlit _ $m) ↪ bvlit $n (zipbits (Stdlib.Bool.xorb) $n $l $m);
rule @bvnot $n (bvlit _ $l) ↪ bvlit $n (zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) $n $l $l);
rule @concat $m $n (bvlit _ $l) (bvlit _ $l') ↪ bvlit ($m + $n) (fit $n $l' ++ take $m $l);
rule @extract $n $i $j (bvlit _ $l) ↪ bvlit ($i - $j + 1) (take ($i - $j + 1) (drop $j (take $n $l)));
rule @zero_extend $n $k (bvlit _ $l) ↪ bvlit ($k + $n) (fit $n $l ++ nseq $k false);

/* ------------------------------------------------------------------------
   Bits of concat/extract with the side condition decided, and cvc5's
   bit-blasting of the bitwise operators (after the literal rules: their
   proofs compute through them)
   ------------------------------------------------------------------------ */

// cellwise connective on two proposition lists (cvc5's bit-blasting of bvor/bvand/bvxor)
symbol pzip : (Prop → Prop → Prop) → 𝕃 o → 𝕃 o → 𝕃 o;
rule pzip _ □ □ ↪ □
with pzip $op ($a ⸬ $l) ($b ⸬ $m) ↪ ($op $a $b) ⸬ pzip $op $l $m;

/* ---------------- helpers ---------------- */

// `n ≤ b` refutes the Boolean `b < n` (`b < n ≡ b +1 ≤ n`, so both together
// give `b +1 ≤ b`, i.e. `b < b`).
opaque symbol bits2_lt_false b n : π (istrue (n ≤ b)) → π ((b < n) = false) ≔
begin
  assume b n h;
  apply ¬istrue=false; assume hlt;
  refine ltnn b (@leq_trans (b +1) n b hlt h)
end;

/* ---------------- bits of concat / extract, one side each ---------------- */

opaque symbol bit_of_concat_lo m n (x : τ (bitvec m)) (y : τ (bitvec n)) b : π (istrue (b < n)) → π (bit_of b (concat x y) = bit_of b y) ≔
begin
  assume m n x y b h;
  rewrite bit_of_concat m n x y b;
  rewrite (istrue=true h);
  reflexivity
end;

opaque symbol bit_of_concat_hi m n (x : τ (bitvec m)) (y : τ (bitvec n)) b : π (istrue (n ≤ b)) → π (bit_of b (concat x y) = bit_of (b - n) x) ≔
begin
  assume m n x y b h;
  rewrite bit_of_concat m n x y b;
  rewrite (bits2_lt_false b n h);
  reflexivity
end;

opaque symbol bit_of_extract_in n i j (x : τ (bitvec n)) b : π (istrue (b < i - j + 1)) → π (bit_of b (extract i j x) = bit_of (j + b) x) ≔
begin
  assume n i j x b h;
  rewrite bit_of_extract n i j x b;
  rewrite (istrue=true h);
  reflexivity
end;

opaque symbol bit_of_extract_out n i j (x : τ (bitvec n)) b : π (istrue (i - j + 1 ≤ b)) → π (bit_of b (extract i j x) = ⊥) ≔
begin
  assume n i j x b h;
  rewrite bit_of_extract n i j x b;
  rewrite (bits2_lt_false b (i - j + 1) h);
  reflexivity
end;

/* ---------------- cvc5's cellwise bit-blasting of the bitwise operators ---------------- */

// `map pb` turns a cellwise propositional connective into `zipbits` of the
// Boolean one, when `pb` is a homomorphism for it. Induction on L with M
// general; the mismatched shapes contradict the size hypothesis.
opaque symbol pzip_map_pb op (opb : 𝔹 → 𝔹 → 𝔹) : (Π p q, π (pb (op p q) = opb (pb p) (pb q))) → Π L M, π (size L = size M) → π (map pb (pzip op L M) = zipbits opb (size L) (map pb L) (map pb M)) ≔
begin
  assume op opb hop; induction
  { induction
    { assume hs; reflexivity }
    { assume b M ihM hs; refine ⊥ₑ (0≠s [size M] hs) } }
  { assume a L ih; induction
    { assume hs; refine ⊥ₑ (s≠0 [size L] hs) }
    { assume b M ihM hs;
      have hs' : π (size L = size M) { refine +1_inj hs };
      change π (pb (op a b) ⸬ map pb (pzip op L M)
               = opb (pb a) (pb b) ⸬ zipbits opb (size L) (map pb L) (map pb M));
      rewrite ih M hs'; rewrite hop a b; reflexivity } }
end;

opaque symbol bb_or n L M : π (size L = n) → π (size M = n) → π (bvor (bbterm n L) (bbterm n M) = bbterm n (pzip (∨) L M)) ≔
begin
  assume n L M hL hM;
  have hs : π (size L = size M) { rewrite hL; rewrite hM; reflexivity };
  have e : π (map pb (pzip (∨) L M) = zipbits (Stdlib.Bool.or) n (map pb L) (map pb M))
    { rewrite left hL; refine pzip_map_pb (∨) (Stdlib.Bool.or) pb_or L M hs };
  change π (bvlit n (zipbits (Stdlib.Bool.or) n (map pb L) (map pb M)) = bvlit n (map pb (pzip (∨) L M)));
  rewrite e; reflexivity
end;

opaque symbol bb_and n L M : π (size L = n) → π (size M = n) → π (bvand (bbterm n L) (bbterm n M) = bbterm n (pzip (∧) L M)) ≔
begin
  assume n L M hL hM;
  have hs : π (size L = size M) { rewrite hL; rewrite hM; reflexivity };
  have e : π (map pb (pzip (∧) L M) = zipbits (Stdlib.Bool.and) n (map pb L) (map pb M))
    { rewrite left hL; refine pzip_map_pb (∧) (Stdlib.Bool.and) pb_and L M hs };
  change π (bvlit n (zipbits (Stdlib.Bool.and) n (map pb L) (map pb M)) = bvlit n (map pb (pzip (∧) L M)));
  rewrite e; reflexivity
end;

opaque symbol bb_xor n L M : π (size L = n) → π (size M = n) → π (bvxor (bbterm n L) (bbterm n M) = bbterm n (pzip xor L M)) ≔
begin
  assume n L M hL hM;
  have hs : π (size L = size M) { rewrite hL; rewrite hM; reflexivity };
  have e : π (map pb (pzip xor L M) = zipbits (Stdlib.Bool.xorb) n (map pb L) (map pb M))
    { rewrite left hL; refine pzip_map_pb xor (Stdlib.Bool.xorb) pb_xor L M hs };
  change π (bvlit n (zipbits (Stdlib.Bool.xorb) n (map pb L) (map pb M)) = bvlit n (map pb (pzip xor L M)));
  rewrite e; reflexivity
end;

// `map pb` of the cellwise negation is the literal rule's `zipbits (λ a _, not a)`
// of the digit list with itself.
opaque symbol bits2_map_not L : π (map pb (map (λ p, ¬ p) L) = zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) (size L) (map pb L) (map pb L)) ≔
begin
  induction
  { reflexivity }
  { assume a L ih;
    change π (pb (¬ a) ⸬ map pb (map (λ p, ¬ p) L)
             = Stdlib.Bool.not (pb a) ⸬ zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) (size L) (map pb L) (map pb L));
    rewrite ih; rewrite pb_not a; reflexivity }
end;

opaque symbol bb_not n L : π (size L = n) → π (bvnot (bbterm n L) = bbterm n (map (λ p, ¬ p) L)) ≔
begin
  assume n L hL;
  have e : π (map pb (map (λ p, ¬ p) L) = zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) n (map pb L) (map pb L))
    { rewrite left hL; refine bits2_map_not L };
  change π (bvlit n (zipbits (λ (a _ : 𝔹), Stdlib.Bool.not a) n (map pb L) (map pb L)) = bvlit n (map pb (map (λ p, ¬ p) L)));
  rewrite e; reflexivity
end;

/* ------------------------------------------------------------------------
   The digits of a natural number, and a literal as a class
   ------------------------------------------------------------------------ */

// The n digits of c, least significant first.
symbol nat2bits : ℕ → ℕ → 𝕃 bool;
rule nat2bits 0 _ ↪ □
with nat2bits ($n +1) $c ↪ odd $c ⸬ nat2bits $n (div2 $c);

opaque symbol class_trunc n (a : ℕ) : π (class (≈ n) (trunc n a) = class (≈ n) a) ≔
begin
  assume n a; apply sound; simplify π; refine trunc_idem n a
end;

opaque symbol bits2natB_nat2bits n c : π (bits2natB (nat2bits n c) = trunc n c) ≔
begin
  induction
  { assume c; reflexivity }
  { assume n ih c; refine feq (λ z, (if (odd c) 1 0) + 2 * z) (ih (div2 c)) }
end;

opaque symbol size_nat2bits n c : π (size (nat2bits n c) = n) ≔
begin
  induction
  { assume c; reflexivity }
  { assume n ih c; refine feq (λ z, z +1) (ih (div2 c)) }
end;

opaque symbol bvlit_nat2bits n c : π (bvlit n (nat2bits n c) = class (≈ n) c) ≔
begin
  assume n c;
  rewrite bvlit_def n (nat2bits n c);
  rewrite bits2natB_nat2bits n c;
  refine class_trunc n c
end;

opaque symbol bvlit_class n l : π (bvlit n l = class (≈ n) (bits2natB l)) ≔
begin
  assume n l; refine bvlit_def n l
end;

/* ------------------------------------------------------------------------
   Sanity checks.
   ------------------------------------------------------------------------ */

// 1. Carrier and width inference.
assert (x : τ (bitvec 8)) ⊢ bvadd x (bvlit 8 (true ⸬ □)) : τ (bitvec 8);
assert (x : τ (bitvec 8)) ⊢ bit_of 0 x : Prop;
assert (x : τ (bitvec 8)) ⊢ extract 7 2 x : τ (bitvec 6);
assert (a : τ (bitvec 1)) (b : τ (bitvec 6)) (c : τ (bitvec 2)) ⊢ concat (concat a b) c : τ (bitvec 9);
assert (y : τ (bitvec 1)) ⊢ zero_extend 63 y : τ (bitvec 64);
assert (y : τ (bitvec 1)) ⊢ concat (bvlit 63 (nseq 63 false)) y : τ (bitvec 64);

// 2. Rules on `cl` compute on closed representatives.
assert ⊢ bvadd (class (≈ 8) 255) (class (≈ 8) 1) ≡ class (≈ 8) 0;
assert ⊢ bvand (class (≈ 4) 12) (class (≈ 4) 10) ≡ class (≈ 4) 8;
assert ⊢ extract 3 2 (class (≈ 4) 5) ≡ class (≈ 2) 1;
assert ⊢ concat (class (≈ 2) 1) (class (≈ 2) 2) ≡ class (≈ 4) 6;

// 3. Bit-blasted constants are literals by computation; literals compute on digit lists.
assert ⊢ bbterm 4 (⊤ ⸬ ⊤ ⸬ ⊥ ⸬ ⊥ ⸬ □) ≡ bvlit 4 (true ⸬ true ⸬ false ⸬ false ⸬ □);
assert ⊢ bit_of 0 (bvlit 1 (true ⸬ □)) ≡ ⊤;
assert ⊢ bit_of 1 (bvlit 2 (true ⸬ false ⸬ □)) ≡ ⊥;
// 3 + 5 = 8 and 15 + 1 = 0 in 4 bits
assert ⊢ bvadd (bvlit 4 (true ⸬ true ⸬ false ⸬ false ⸬ □)) (bvlit 4 (true ⸬ false ⸬ true ⸬ false ⸬ □))
       ≡ bvlit 4 (false ⸬ false ⸬ false ⸬ true ⸬ □);
assert ⊢ bvadd (bvlit 4 (true ⸬ true ⸬ true ⸬ true ⸬ □)) (bvlit 4 (true ⸬ false ⸬ false ⸬ false ⸬ □))
       ≡ bvlit 4 (false ⸬ false ⸬ false ⸬ false ⸬ □);
// -1 = 15 in 4 bits; 2 - 3 = 15
assert ⊢ bvneg (bvlit 4 (true ⸬ false ⸬ false ⸬ false ⸬ □)) ≡ bvlit 4 (true ⸬ true ⸬ true ⸬ true ⸬ □);
assert ⊢ bvsub (bvlit 4 (false ⸬ true ⸬ false ⸬ false ⸬ □)) (bvlit 4 (true ⸬ true ⸬ false ⸬ false ⸬ □))
       ≡ bvlit 4 (true ⸬ true ⸬ true ⸬ true ⸬ □);
assert ⊢ bvand (bvlit 4 (false ⸬ false ⸬ true ⸬ true ⸬ □)) (bvlit 4 (false ⸬ true ⸬ false ⸬ true ⸬ □))
       ≡ bvlit 4 (false ⸬ false ⸬ false ⸬ true ⸬ □);
assert ⊢ concat (bvlit 2 (true ⸬ false ⸬ □)) (bvlit 2 (false ⸬ true ⸬ □)) ≡ bvlit 4 (false ⸬ true ⸬ true ⸬ false ⸬ □);
assert ⊢ extract 2 1 (bvlit 4 (false ⸬ true ⸬ true ⸬ false ⸬ □)) ≡ bvlit 2 (true ⸬ true ⸬ □);
assert ⊢ zero_extend 2 (bvlit 2 (true ⸬ false ⸬ □)) ≡ bvlit 4 (true ⸬ false ⸬ false ⸬ false ⸬ □);
// 4. Wide constants are cheap: 2^31 in 32 bits, extracted and compared.
assert ⊢ extract 31 1 (bvlit 32 (true ⸬ nseq 31 false)) ≡ bvlit 31 (nseq 31 false);
assert ⊢ extract 31 31 (bvlit 32 (nseq 31 false ++ (true ⸬ □))) ≡ bvlit 1 (true ⸬ □);
assert ⊢ eq_refl (bvlit 32 (nseq 31 false ++ (true ⸬ □)))
       : π (bvlit 32 (nseq 31 false ++ (true ⸬ □)) = bvlit 32 (nseq 31 false ++ (true ⸬ □)));
assert ⊢ zero_extend 16 (bvlit 16 (true ⸬ nseq 15 false)) ≡ bvlit 32 (true ⸬ nseq 31 false);
