require open Stdlib.Bool;
require open Stdlib.Eq;
require open Stdlib.Set;
require open Stdlib.Pos;
require open Stdlib.Prop;
require open Stdlib.Comp;
require open Stdlib.Z;
require open lambdapi.Classic;
require open lambdapi.Alethe;
require open lambdapi.Q;

constant symbol R : TYPE;

constant symbol cst: ℚ → R;

symbol var : ℚ → ℚ → R;
/* semantics: [var k x] = k * x
note that the second argument could be any type that has a ring structure
(we then would take R : TYPE → TYPE) */
symbol opp:R → R;
symbol add:R → R → R;

symbol mul: ℚ → R → R;
rule mul $k (var $l $i) ↪ var ($k q*' $l) $i
with mul $k (opp $r) ↪ mul (q~ $k) $r
with mul $k (add $x $y) ↪ add (mul $k $x) (mul $k $y)
with mul $k (cst $c) ↪ cst ($k q*' $c)
with mul $k (mul $l $z) ↪ mul ($k q*' $l) $z;

rule var 0 _ ↪ cst 0;
rule opp (var $k $x) ↪ var (q~ $k) $x
with opp (cst $k) ↪ cst (q~ $k)
with opp (opp $x) ↪ $x
with opp (add $x $y) ↪ add (opp $x) (opp $y);
// // // note that opp is totally defined on terms built with var, cst, opp and add, i.e. no normal form contains opp
rule add (var $c1 $i) (var $c2 $i) ↪ (var ($c1 q+' $c2) $i)
with add (var $c1 $i) (add (var $c2 $i) $y) ↪ (add (var ($c1 q+' $c2) $i) $y)
with add (cst $k) (cst $l) ↪ cst ($k q+' $l)
with add (cst $k) (add (cst $l) $y) ↪ add (cst ($k q+' $l)) $y
with add (cst 0) $x ↪ $x
with add $x (cst 0) ↪ $x
;


sequential symbol reify : ℚ → R;
rule reify (0 # $x) ↪ cst (0 # $x)
with reify (Qmake 0 $x) ↪  cst (0 # $x)
with reify ($x q+ $y) ↪ add (reify $x) (reify $y)
with reify ((Qmake (Zpos $x) $p) q* $y) ↪ mul (Qmake (Zpos $x) $p) (reify $y)
with reify ((Qmake (Zneg $x) $p) q* $y) ↪ mul (Qmake (Zneg $x) $p) (reify $y)
with reify ((Qmake Z0 $p) q* $y) ↪ cst (0 # H)
with reify $a ↪ var (inject_Z 1) $a
;

// Lemma Zle_not_gt n m : n q<= m q-q> q~ n q> m.
symbol Qle_not_gt n m:  πᶜ ((n q≤ m) = ¬ (n q> m));

symbol Qlt_not_ge n m:  πᶜ ((n q< m) = ¬ (n q≥ m));

symbol Qge_not_lt : Π n: ℚ, Π m: ℚ, πᶜ ((n q≥ m) = ¬ (n q< m));

symbol Qgt_not_le : Π n: ℚ, Π m: ℚ, πᶜ ((n q> m) = ¬ (n q≤ m));

// // Lemma Qmult_gt_compat_r n m p : p q> 0 q-q> n q> m q-q> n * p q> m * p.
symbol Qmult_gt_compat c a b : πᶜ (c q> 0) → πᶜ (a q> b) → πᶜ (c q* a q> c q* b) ;

// // Lemma Qmult_ge_compat_r n m p : n q>= m q-q> p q>= 0 q-q> n * p q>= m * p.
symbol Qmult_ge_compat c a b : π (c q> 0) → π (a q≥ b) → π (c q* a q≥ c q* b);

symbol Qgt_le_succ_r a b: πᶜ (a q> b) → πᶜ (a q≥ b q+ 1);

symbol Qinv_lt a b: πᶜ (a q< b) → πᶜ (q~ a q> q~ b);

symbol Qsum_geq_s [a b c d]: πᶜ (a q≥ b) → πᶜ (c q≥ d) → πᶜ (a q+ c q≥ b q+ d);

symbol Q_diff_geq_Q0 a b: πᶜ (a q≥ b) → πᶜ (a q- b q≥ 0);
symbol Q_diff_gt_Q0 a b: πᶜ (a q> b) → πᶜ (a q- b q> 0);



symbol Qinv_lt_eq a b: πᶜ ((a q< b) = (q~ a q> q~ b));

symbol Qinv_le_eq a b: πᶜ ((a q≤ b) = (q~ a q≥ q~ b));

symbol Q_diff_geq_Q0_eq a b: πᶜ ((a q≥ b) = (a q- b q≥ 0));

symbol Q_diff_gt_Q0_eq a b: πᶜ ((a q> b) = (a q- b q> 0));

symbol Q_diff_eq_Q0_eq a b: πᶜ ((a = b) = (a q- b = (0 # H)));

symbol strengthen a b: πᶜ ((a q> b) = (a q≥ b q+ 1));

//symbol Q_eq_antisym [a b: τ rational]: πᶜ (a = b) → πᶜ ((a q≤ b) ∧ᶜ (a q≥ b));

// //Axioms
symbol Q_eq_antisym (a b: τ rational):  πᶜ ((¬ (a = b)) = ¬ (a q≥ b));

symbol Qmult_eq_compat_eq (c a b: τ rational) : πᶜ ((¬ (a = b)) = ¬ (c q* a = c q* b));
symbol Qmult_gt_compat_eq (c a b: τ rational) : πᶜ (¬ (a q> b) = ¬ (c q* a q> c q* b)) ;
symbol Qmult_ge_compat_eq (c a b: τ rational) : πᶜ (¬ (a q≥ b) = ¬ (c q* a q≥ c q* b)) ;

opaque q>;
opaque q≥;

///////////////////// Alethe rules for linear arithmetic rules  ////////////////////

opaque symbol la_disequality [t1 t2] : π̇ ((t1 = t2) ∨ᶜ ¬ (t1 ≤ t2) ∨ᶜ ¬ (t2 ≤ t1) ⟇ ▩) ≔ begin admit end;

opaque symbol la_totality [t1 t2] : π̇ ((t1 ≤ t2) ∨ᶜ (t2 ≤ t1) ⟇ ▩) ≔ begin admit end;

opaque symbol la_rw_eq [u t] : π̇ ((u = t) = ((u ≤ t) ∧ᶜ (t ≤ u)) ⟇ ▩) ≔ begin admit end;



symbol denoteQ: R → ℚ;
rule denoteQ (var $k $i) ↪ $k q*' $i
with denoteQ (cst $k) ↪ Qred $k
with denoteQ (add $x $y) ↪ (denoteQ $x) q+' (denoteQ $y);

symbol inj: Π x: ℚ, πᶜ ((denoteQ (reify x)) = x);


///////////////////// Example ////////////////////

//FIXME: Finish la_generic
// Example 11.2: The following la_generic step is from a QF_UFLIA problem
opaque symbol {| Example 11.2 |} (f3: ℤ) : πᶜ (¬ (f3 q≤ 0) ∨ᶜ (1 q+ (4 q* f3) q≤ 1)) ≔
begin
assume f3;
// // step 1
rewrite Qle_not_gt (1 q+ (4 q* f3)) 1;
// // step ??
rewrite Qinv_le_eq f3 0;
// // step 3: After normalization we get − f3 
rewrite Q_diff_geq_Q0_eq (q~ f3) (q~ 0);
rewrite Q_diff_gt_Q0_eq (1 q+ (4 q* f3)) 1;
// // step 4
rewrite strengthen;
// // step 5 args: [1,  1/4]
rewrite (Qmult_ge_compat_eq 1 (q~ (Qmake f3 H) q- q~ (Qmake 0 H)) 0);
rewrite (Qmult_ge_compat_eq (1 # O (O H)) ((Qmake 1 H q+ (Qmake 4 H q* Qmake f3 H)) q- Qmake 1 H) (Qmake 0 H q+ Qmake 1 H));

rewrite imp_eq_or;
apply ⇒ᶜᵢ; assume H1;
apply ¬ᶜᵢ; assume H2;
compute (reify ((Qmake _1 H q* (q~ (Qmake f3 H) q- q~ (Qmake 0 H))) q+ ((_1 # O (O H)) q* ((Qmake _1 H q+ (Qmake _4 H q* Qmake f3 H)) q- Qmake _1 H))));
// set H1l ≔  (Qmake 1 H) q* (q~ (Qmake f3 H) q- q~ (Qmake 0 H));
// set H1r ≔  (Qmake 1 H) q* 0;
// set H2l ≔  (1 # O (O H)) q* ((Qmake 1 H q+ (Qmake 4 H q* Qmake f3 H)) q- Qmake 1 H);
// set H2r ≔  (1 # O (O H)) q* ( 0 q+ 1 );
// have Hsum: πᶜ (
//     (Qmake _1 1 q* (q~ (Qmake f3 1) q- q~ (Qmake 0 1))) q+ ((_1 # 4) q* ((Qmake _1 1 q+ (Qmake _4 1 q* Qmake f3 1)) q- Qmake _1 1))
        //q≥
// ) {
// };
// compute  H1r q+ H2r; // = 1/4
// compute H1l q+ H2l;
// admit
admit
end;


// symbol la_example : πᶜ (
//     ¬ ((q~ 1) q* F = (q~ 1 q* 10)) ∨ᶜ
//     ¬ (F q< 5) ∨ᶜ
//     ((q~ 1 q* F) q+ F q< (q~ 1 q* 10) q+ 5)
// ) ≔
// begin
// // // step 1
// rewrite .[x in _ ∨ᶜ _ ∨ᶜ x ] Qlt_not_ge;
// // // step 2
// rewrite Qinv_lt_eq;
// // // step 3
// rewrite Q_diff_geq_Q0_eq;
// rewrite Q_diff_gt_Q0_eq;
// // // step 4
// rewrite strengthen;
// // // step 5
// rewrite (Qmult_eq_compat_eq (q~ 1) ((q~ 1) q* F) ((q~ 1) q* 10));
// rewrite (Qmult_ge_compat_eq 1 (q~ F q- q~ 5) (0 q+ 1));
// rewrite (Qmult_ge_compat_eq 1 (((q~ 1 q* F) q+ F) q- ((q~ 1 q* 10) q+ 5)) 0);
// rewrite Q_eq_antisym;
// //step 2
// rewrite imp_eq_or;
// apply ⇒ᶜᵢ; assume H1;
// rewrite imp_eq_or;
// apply ⇒ᶜᵢ; assume H2;
// apply ¬ᶜᵢ; assume H3;
// set H1l ≔ (q~ 1 q* (q~ 1 q* F));
// set H1r ≔ (q~ 1 q* (q~ 1 q* 10));
// set H2l ≔ (1 q* (q~ F q- q~ 5));
// set H2r ≔ ((0 q+ 1));
// set H3l ≔ (1 q* (((q~ 1 q* F) q+ F) q- ((q~ 1 q* 10) q+ 5)));
// set H3r ≔ (0);
// //step 5
// have Hsum: πᶜ (H1l q+ H2l q+ H3l q≥ H1r q+ H2r q+ H3r) { 
//     apply Qsum_geq_s (Qsum_geq_s H1 H2) H3;
// };
// admit
// end;


