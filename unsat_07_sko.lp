require open Stdlib.Prop;

require open Stdlib.FOL;

require open Stdlib.Set;

require open Stdlib.Eq;

require open Stdlib.List;

require open lambdapi.Alethe;

symbol U : TYPE;

rule U ↪ τ o;

symbol a : U;

symbol b : U;

symbol p : U → Prop;

constant symbol h1 : π̇ ((¬ᶜ ((((`∀ᶜ x1, (¬ᶜ ((p x1))))) ⟹ᶜ ((¬ᶜ ((`∃ᶜ x1,(p x1)))))))) ⟇ ▩);

constant symbol h2 : π̇ (((¬ᶜ ((`∃ᶜ x1,(p x1)))) ⟺ᶜ ⊤) ⟇ ▩);

//symbol sko_ex: 

opaque symbol unsat_07_sko : π̇ ▩ ≔ 
begin

// (step t29 ...)

// (anchor :step t30 :args ((:= veriT_vr3 (choice ((veriT_vr3 U)) (p veriT_vr3)))))
// (step t30.t1 (cl (= veriT_vr3 (choice ((veriT_vr3 U)) (p veriT_vr3)))) :rule refl)
// (step t30.t2 (cl (= (p veriT_vr3) (p (choice ((veriT_vr3 U)) (p veriT_vr3))))) :rule cong :premises (t30.t1))
// (step t30 (cl (= (exists ((veriT_vr3 U)) (p veriT_vr3)) (p (choice ((veriT_vr3 U)) (p veriT_vr3))))) :rule sko_ex)
have t30 : Π veriT_vr3, π (veriT_vr3 = (`ϵ veriT_vr3, (p veriT_vr3))) →  π̇ (((`∃ᶜ veriT_vr3,(p veriT_vr3)) ⟺ᶜ (p (`ϵ veriT_vr3, (p veriT_vr3)))) ⟇ ▩) {
    assume veriT_vr3 H;
    have t30_t1 : π̇ ((veriT_vr3 ⟺ᶜ `ϵ veriT_vr3, (p veriT_vr3)) ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        rewrite H;
        apply ⟺ᶜ_refl;
    };
    have t30_t2 : π̇ (((p veriT_vr3) ⟺ᶜ (p `ϵ veriT_vr3, (p veriT_vr3))) ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        apply cong p (π̇ₗ t30_t1);
    };
    have t30 : π̇ (((`∃ᶜ veriT_vr3,(p veriT_vr3)) ⟺ᶜ (p `ϵ veriT_vr3, (p veriT_vr3))) ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        apply ϵ_equiv_∃ᶜ
    };
    apply t30
};

// (step t31 (cl (= (and (forall ((veriT_vr2 U)) (not (p veriT_vr2))) (exists ((veriT_vr3 U)) (p veriT_vr3))) (and (forall ((veriT_vr2 U)) (not (p veriT_vr2))) (p (choice ((veriT_vr3 U)) (p veriT_vr3)))))) :rule cong :premises (t30))

have t31 : π̇ ((((`∀ᶜ veriT_vr2, (¬ᶜ ((p veriT_vr2)))) ∧ᶜ (`∃ᶜ veriT_vr3,(p veriT_vr3)) ∧ᶜ ⊤) ⟺ᶜ ((`∀ᶜ veriT_vr2, (¬ᶜ ((p veriT_vr2)))) ∧ᶜ (p `ϵ veriT_vr3, (p veriT_vr3)) ∧ᶜ ⊤))
        ⟇ ▩) {
    have tmp: π (((`∀ᶜ veriT_vr2, (¬ᶜ ((p veriT_vr2)))) ⟺ᶜ (`∀ᶜ veriT_vr2, (¬ᶜ ((p veriT_vr2)))))) {
        apply ⟺ᶜ_refl;
    };
    apply ∨ᶜᵢ₁;
    apply cong2 (∧ᶜ) tmp;
    apply cong2 (∧ᶜ) (π̇ₗ (t30 (`ϵ veriT_vr3, (p veriT_vr3)) (eq_refl (`ϵ veriT_vr3, p veriT_vr3))));
    apply ⟺ᶜ_refl;
};

// (step 32 ...)
end;