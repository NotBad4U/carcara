require open Stdlib.Prop;
require open Stdlib.FOL;
require open Stdlib.Eq;
require open Stdlib.Nat;
require Stdlib.Bool;
require open Stdlib.Set;
require open Stdlib.List;
require open lambdapi.Alethe;
require open lambdapi.Classic;

inductive prop: TYPE ≔
| pTrue: prop
| pFalse: prop
| pAnd: prop → prop → prop
| pOr: prop → prop → prop
| pNeg: prop → prop
;

symbol propS: Set;

rule τ propS ↪ prop;


// A denotation function converts our syntax into a semantic value
// The σ is the context which contains the mapping from variables to Props.
symbol prop_denote (p: prop): Prop;
rule prop_denote pTrue ↪ ⊤
with prop_denote pFalse ↪ ⊥
with prop_denote (pAnd $x $y) ↪  (prop_denote $x) ∧ᶜ (prop_denote $y)
with prop_denote (pOr $x $y) ↪  (prop_denote $x) ∨ᶜ (prop_denote $y)
;

open Stdlib.Bool;

sequential symbol prop_eq (l r: prop): τ bool;
rule prop_eq pTrue pTrue ↪ true
with prop_eq pFalse pFalse ↪ true
with prop_eq (pAnd $a $b) (pAnd $c $d) ↪ (prop_eq $a $c) and (prop_eq $b $d)
with prop_eq (pOr $a $b) (pOr $c $d) ↪ (prop_eq $a $c) and (prop_eq $b $d)
with prop_eq (pNeg $a) (pNeg $b) ↪ prop_eq $a $b
with prop_eq $x $y ↪ false
;

symbol provable (goal: prop) : 𝔹;
rule provable pTrue ↪ true
with provable pFalse  ↪ false
with provable (pAnd $l $r)  ↪ (provable $l ) and (provable $r )
with provable (pOr $l $r)  ↪ (provable $l ) or (provable $r )
with provable (pNeg $x)  ↪ not (provable $x);

opaque symbol provable_sound: Π (goal: prop), πᶜ (provable goal = true) → πᶜ (prop_denote goal) ≔
begin admit end;

opaque symbol convert_prop: Π (goal: prop), πᶜ (prop_denote goal) ≔
begin admit end;





