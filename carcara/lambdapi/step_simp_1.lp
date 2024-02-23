require open Stdlib.Prop;

require open Stdlib.Set;

require open Stdlib.Eq;

require open Stdlib.Nat;

require open lambdapi.Classic;

require open lambdapi.Alethe;

require open lambdapi.Simplify;

require open lambdapi.Rare;

symbol S : TYPE;

rule S ↪ τ o;

symbol A : S;

symbol f : S → Prop;

symbol g : S → Prop;

constant symbol h1 : π̇ ((¬ ((¬ ((¬ ((¬ ((f A))))))))) ⟇ ▩);

constant symbol h6 : π̇ ((g A) ⟇ ▩);

constant symbol h7 : π̇ (((¬ ((g A))) ∨ᶜ (¬ ((f A))) ∨ᶜ (¬ ((f A))) ∨ᶜ ⊥) ⟇ ▩);

opaque symbol step_simp_1 : π̇ ▩ ≔ 
begin
have t2 : π̇ ((¬ ((¬ ((¬ ((¬ ((¬ ((f A)))))))))))  ⟇ (¬ ((¬ ((f A))))) ⟇ ▩) {
    apply not_not;
};
have t3 : π̇ ((¬ ((¬ ((f A))))) ⟇ ▩) {
    have t2_h1 : π̇ ((¬ ((¬ ((f A))))) ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2 h1;
    };
    refine t2_h1;
};
have t4 : π̇ ((¬ ((¬ ((¬ ((f A)))))))  ⟇ (f A) ⟇ ▩) {
    apply not_not;
};
have t5 : π̇ ((f A) ⟇ ▩) {
    have t4_t3 : π̇ ((f A) ⟇ ▩) {
        apply resolutionᵣ _ _ _ t4 t3;
    };
    refine t4_t3;
};
have t8 : π̇ ((((¬ ((g A))) ∨ᶜ (¬ ((f A))) ∨ᶜ (¬ ((f A))) ∨ᶜ ⊥) = ((¬ ((g A))) ∨ᶜ (¬ ((f A))) ∨ᶜ ⊥)) ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    try rewrite or_identity ;
    try rewrite and_identity ;
    try rewrite ac_simp_or ;
    try rewrite ac_simp_and ;
    reflexivity;
};
have t9 : π̇ ((¬ ((((¬ ((g A))) ∨ᶜ (¬ ((f A))) ∨ᶜ (¬ ((f A))) ∨ᶜ ⊥) = ((¬ ((g A))) ∨ᶜ (¬ ((f A))) ∨ᶜ ⊥))))
         ⟇ (¬ (((¬ ((g A))) ∨ᶜ (¬ ((f A))) ∨ᶜ (¬ ((f A))) ∨ᶜ ⊥)))
         ⟇ ((¬ ((g A))) ∨ᶜ (¬ ((f A))) ∨ᶜ ⊥)
        ⟇ ▩) {
    apply equiv_pos2;
};
have t10 : π̇ (((¬ ((g A))) ∨ᶜ (¬ ((f A))) ∨ᶜ ⊥) ⟇ ▩) {
    have t9_t8 : π̇ ((¬ (((¬ ((g A))) ∨ᶜ (¬ ((f A))) ∨ᶜ (¬ ((f A))) ∨ᶜ ⊥)))  ⟇ ((¬ ((g A))) ∨ᶜ (¬ ((f A))) ∨ᶜ ⊥) ⟇ ▩) {
        apply resolutionᵣ _ _ _ t9 t8;
    };
    have t9_t8_h7 : π̇ (((¬ ((g A))) ∨ᶜ (¬ ((f A))) ∨ᶜ ⊥) ⟇ ▩) {
        apply resolutionᵣ _ _ _ t9_t8 h7;
    };
    refine t9_t8_h7;
};
have t11 : π̇ ((¬ ((g A)))  ⟇ (¬ ((f A))) ⟇ ▩) {
    apply π̇ₗ t10;
};
have t12 : π̇ ▩ {
    have t11_t5 : π̇ ((¬ ((g A))) ⟇ ▩) {
        have t11' : (π̇ ((¬ ((g A)))  ⟇ (¬ ((f A))) ⟇ ▩) → π̇ ((¬ ((f A)))  ⟇ (¬ ((g A))) ⟇ ▩)) {
            assume H2;
            apply ⟇ₑ H2 
            {
                assume H;
                apply ⟇ᵢ₂;
                apply H;
            }
            {
                assume H1;
                apply ⟇ᵢ₁;
                apply H1;
            };
        };
        apply resolutionᵣ _ _ _ (t11' t11) t5;
    };
    have t11_t5_h6 : π̇ ▩ {
        apply resolutionᵣ _ _ _ t11_t5 h6;
    };
    refine t11_t5_h6;
};
apply t12;
end;