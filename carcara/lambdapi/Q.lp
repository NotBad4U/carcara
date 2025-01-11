require open Stdlib.Prop;
require open Stdlib.FOL;
require open Stdlib.Eq;
require open Stdlib.Set;
require open Stdlib.Z;
require open Stdlib.Pos;
require open Stdlib.Bool;
require open lambdapi.Classic;
require open lambdapi.Alethe;

inductive ℚ : TYPE ≔
|  Qmake : ℤ → ℙ → ℚ;

constant symbol rational : Set;

rule τ rational ↪ ℚ;

symbol # (z: ℤ) (p: ℙ) ≔ Qmake z p;
notation # infix 30;

symbol inject_Z (x: ℤ) ≔  Qmake x H;

coerce_rule coerce ℤ ℚ $x ↪ inject_Z $x;

constant symbol JMeq : Π [a], Π (x: τ a), Π [b], τ b → Prop;

symbol Rat_to_Int: Π x: ℤ, πᶜ (JMeq (x # H) x);

symbol Qnum (q: ℚ): ℤ;
rule Qnum (Qmake $z $p) ↪ $z;

symbol Qden (q: ℚ): ℙ;
rule Qden (Qmake $z $p) ↪ $p;

symbol QDen (q: ℚ): ℤ ≔ Zpos (Qden q);

symbol 𝕢≐ (p q : ℚ) ≔ (Qnum p) × (QDen q) ≐ (Qnum q) × (QDen p); notation 𝕢≐ infix 10;

symbol 𝕢= (p q : ℚ) ≔ (Qnum p) × (QDen q) = (Qnum q) × (QDen p); notation 𝕢= infix 10;

symbol 𝕢≤ (p q : ℚ) ≔ ((Qnum p) × (QDen q)) ≤ ((Qnum q) × (QDen p)); notation 𝕢≤ infix 10;

symbol 𝕢< (p q : ℚ) ≔ ((Qnum p) × (QDen q)) < ((Qnum q) × (QDen p)); notation 𝕢< infix 10;

symbol 𝕢≥ (p q : ℚ) ≔ ≥ ((Qnum p) × (QDen q)) ((Qnum q) × (QDen p)); notation 𝕢≥ infix 10;

symbol 𝕢> (p q : ℚ) ≔ ((Qnum p) × (QDen q)) > ((Qnum q) × (QDen p)); notation 𝕢> infix 10;

symbol 𝕢+: ℚ → ℚ → ℚ; notation 𝕢+ infix left 20;
rule $x 𝕢+ $y ↪ ((Qnum $x × QDen $y) + (Qnum $y × QDen $x)) # (mul (Qden $x) (Qden $y));


symbol 𝕢×: ℚ → ℚ → ℚ; notation 𝕢× infix left 22;
rule $x 𝕢× $y ↪ (Qnum $x × Qnum $y) # (mul(Qden $x) (Qden $y));

print ~;

symbol 𝕢~: ℚ → ℚ; notation 𝕢~ prefix 24;
rule 𝕢~ $x ↪ (~ (Qnum $x)) # (Qden $x);


symbol 𝕢-: ℚ → ℚ → ℚ; notation 𝕢- infix left 20;
rule $x 𝕢- $y ↪  $x 𝕢+ (𝕢~ $y);

symbol Qinv: ℚ → ℚ;
rule Qinv (Z0  # $y) ↪ Z0 # H
with Qinv ((Zpos $x) # $y) ↪ (Zpos $y) # $x
with Qinv ((Zneg $x) # $y) ↪ (Zneg $y) # $x;

symbol Qdiv: ℚ → ℚ → ℚ;
rule Qdiv $x $y ↪ $x 𝕢× (Qinv $y);

symbol 1#1 : ℚ ≔ 1 # H;


opaque symbol Qeq_refl [x] : πᶜ (x 𝕢= x) ≔
begin assume x; reflexivity; end;

opaque symbol Qeq_sym [x y] : πᶜ (x 𝕢= y) → πᶜ (y 𝕢= x) ≔
begin assume x y H; symmetry; apply H; end;

opaque symbol Qeq_trans [x y z] : π (x 𝕢= y) → π (y 𝕢= z) → π (x 𝕢= z) ≔
begin admit end;

opaque symbol Qden_cancel a b p : π (((a # p) 𝕢= (b # p)) ⇒ (a = b)) ≔
begin admit end;

opaque symbol Qnum_cancel (z : τ int) (a b : τ pos) : π (z ≠ 0) → π (((z # a) 𝕢= (z # b)) ⇒ (a = b)) ≔
begin admit end;