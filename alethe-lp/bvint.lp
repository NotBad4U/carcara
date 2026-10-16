/*
  The ℤ side of bit-vectors: what cvc5 writes around them in integers.

  - `bvsize x`         cvc5's `@bvsize`, the width as an integer;
  - `bv_of_int w z`    cvc5's `@bv z w` when z is not a numeral (it computes to
                       the literal `bvlit w (…)` once z is closed);
  - `Zpow2`, `Zmod`    `int.pow2` and `mod` on non-negative integers, as cvc5
                       uses them in `bv-concat-merge-const` and `evaluate`.

  Opened when a proof uses bit-vectors and integers both (Module::BvInt). ℤ is
  Stdlib.Z (binary); the conversions go through unary ℕ, which is fine for the
  widths and small values that occur.
*/
require open Stdlib.Pos Stdlib.Z;
require open Stdlib.Bool Stdlib.Nat Stdlib.List;
require open alethe.core;      // ℕ's + * < ≤ are the ones in scope from here
require open Stdlib.Quotient;
require open alethe.bv;
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

// ℕ → ℤ and back (a negative integer reads as 0: cvc5 never passes one here).
symbol Z_of_nat : ℕ → ℤ;
rule Z_of_nat 0 ↪ Z0
with Z_of_nat ($x +1) ↪ (Stdlib.Z.+) (Z_of_nat $x) (Zpos H);

symbol nat_of_Z : ℤ → ℕ;
rule nat_of_Z Z0 ↪ 0
with nat_of_Z (Zpos $p) ↪ val $p
with nat_of_Z (Zneg _) ↪ 0;

assert ⊢ Z_of_nat 5 ≡ Zpos (I (O H));
assert ⊢ nat_of_Z (Zpos (I (O H))) ≡ 5;

// cvc5's `@bvsize x`.
symbol bvsize [n] (x : τ (bitvec n)) : ℤ ≔ Z_of_nat n;

// `int.pow2 k` for a non-negative k.
symbol Zpow2 (z : ℤ) : ℤ ≔ Z_of_nat ((Stdlib.Nat.^) 2 (nat_of_Z z));

// Euclidean remainder on ℕ, by repeated subtraction (the dividend is enough fuel).
symbol nmod_fuel : ℕ → ℕ → ℕ → ℕ;
rule nmod_fuel 0 $x _ ↪ $x
with nmod_fuel ($f +1) $x $m ↪ if ((Stdlib.Nat.<) $x $m) $x (nmod_fuel $f ((Stdlib.Nat.-) $x $m) $m);
symbol nmod (x m : ℕ) : ℕ ≔ nmod_fuel x x m;

assert ⊢ nmod 7 3 ≡ 1;
assert ⊢ nmod 6 3 ≡ 0;
assert ⊢ nmod 0 8 ≡ 0;

// SMT-LIB `mod` on non-negative integers.
symbol Zmod (a b : ℤ) : ℤ ≔ Z_of_nat (nmod (nat_of_Z a) (nat_of_Z b));


// cvc5's `@bv z w` with a symbolic value: the literal, once z is closed.
symbol bv_of_int (w : ℕ) (z : ℤ) : τ (bitvec w) ≔ bvlit w (nat2bits w (nat_of_Z z));

assert ⊢ bv_of_int 5 ((Stdlib.Z.+) ((Stdlib.Z.*) Z0 (Zpow2 (Zpos H))) (Zmod Z0 (Zpow2 (Zpos H))))
       ≡ bvlit 5 (false ⸬ false ⸬ false ⸬ false ⸬ false ⸬ □);
assert ⊢ bv_of_int 4 (Zpos (I (O H))) ≡ bvlit 4 (true ⸬ false ⸬ true ⸬ false ⸬ □);
assert (x : τ (bitvec 32)) ⊢ (Stdlib.Z.-) (bvsize x) (Zpos H) ≡ Z_of_nat 31;
assert ⊢ Zpow2 (Z_of_nat 13) ≡ Z_of_nat 8192;
