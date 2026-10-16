// The cvc5 RARE rewrites over bit-vectors (`bv-*`), on top of alethe.bv.
// Each lemma carries the exact RARE rule name; the translator's RARE_RULES
// registry (src/translation/lambdapi/rules/rare/mod.rs) maps the name here.
require open alethe.core;
require open alethe.bv;

// (define-rule bv-zero-extend-eliminate ((x ?BitVec) (n Int))
//   (zero_extend n x) (concat (@bv 0 n) x))
// Arguments in cvc5's order (x, then the amount), as the translator applies them.
opaque symbol bv-zero-extend-eliminate [n] (x : τ (bitvec n)) k :
  π (zero_extend k x = concat (bvlit k (nseq k false)) x) ≔
begin
  assume n x k; refine zero_extend_concat_zero k x
end;
