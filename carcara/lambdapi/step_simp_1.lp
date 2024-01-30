require open Stdlib.Prop;

require open Stdlib.FOL;

require open Stdlib.Set;

require open Stdlib.Eq;

require open Stdlib.List;

require open Stdlib.Nat;

require open lambdapi.Alethe;

symbol I [a]: ℕ → τ a; 

symbol code_S : Set;
symbol S ≔ τ code_S;
print τ;
//rule S ↪ τ o;

compute τ o;

symbol A : S ≔ I 0;

constant symbol arrow : Set → Set → Set;

symbol prop: Set;

//decoding function 
rule τ (arrow $x $y) ↪ τ $x → τ $y;

//rule τ prop ↪ Prop;

debug +u;

symbol f : S → Prop ≔ @I (arrow code_S o) 1;
//symbol f : S → Prop ≔ I 1;

symbol g : S → Prop;

symbol h: Prop ≔ `∀ᶜ x, f x;

constant symbol h1 : π̇ ((¬ᶜ ((¬ᶜ ((¬ᶜ ((¬ᶜ ((f A))))))))) ⟇ ▩);

constant symbol h6 : π̇ ((g A) ⟇ ▩);

constant symbol h7 : π̇ (((¬ᶜ ((g A))) ∨ᶜ (¬ᶜ ((f A))) ∨ᶜ (¬ᶜ ((f A))) ∨ᶜ ⊥) ⟇ ▩);

opaque symbol step_simp_1 : π̇ ▩ ≔ 
begin
have t2 : π̇ ((¬ᶜ ((¬ᶜ ((¬ᶜ ((¬ᶜ ((¬ᶜ ((f A)))))))))))  ⟇ (¬ᶜ ((¬ᶜ ((f A))))) ⟇ ▩) {
    apply not_not;
};
have t3 : π̇ ((¬ᶜ ((¬ᶜ ((f A))))) ⟇ ▩) {
    have t2_h1 : π̇ ((¬ᶜ ((¬ᶜ ((f A))))) ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2 h1;
    };
    refine t2_h1;
};
have t4 : π̇ ((¬ᶜ ((¬ᶜ ((¬ᶜ ((f A)))))))  ⟇ (f A) ⟇ ▩) {
    apply not_not;
};
have t5 : π̇ ((f A) ⟇ ▩) {
    have t4_t3 : π̇ ((f A) ⟇ ▩) {
        apply resolutionᵣ _ _ _ t4 t3;
    };
    refine t4_t3;
};
have t8 : π̇ ((((¬ᶜ ((g A))) ∨ᶜ (¬ᶜ ((f A))) ∨ᶜ (¬ᶜ ((f A))) ∨ᶜ ⊥) ⟺ᶜ ((¬ᶜ ((g A))) ∨ᶜ (¬ᶜ ((f A))) ∨ᶜ ⊥)) ⟇ ▩) {
    admit;
};
have t9 : π̇ ((¬ᶜ ((((¬ᶜ ((g A))) ∨ᶜ (¬ᶜ ((f A))) ∨ᶜ (¬ᶜ ((f A))) ∨ᶜ ⊥) ⟺ᶜ ((¬ᶜ ((g A))) ∨ᶜ (¬ᶜ ((f A))) ∨ᶜ ⊥))))
         ⟇ (¬ᶜ (((¬ᶜ ((g A))) ∨ᶜ (¬ᶜ ((f A))) ∨ᶜ (¬ᶜ ((f A))) ∨ᶜ ⊥)))
         ⟇ ((¬ᶜ ((g A))) ∨ᶜ (¬ᶜ ((f A))) ∨ᶜ ⊥)
        ⟇ ▩) {
    apply equiv_pos2;
};
have t10 : π̇ (((¬ᶜ ((g A))) ∨ᶜ (¬ᶜ ((f A))) ∨ᶜ ⊥) ⟇ ▩) {
    have t9_t8 : π̇ ((¬ᶜ (((¬ᶜ ((g A))) ∨ᶜ (¬ᶜ ((f A))) ∨ᶜ (¬ᶜ ((f A))) ∨ᶜ ⊥)))
             ⟇ ((¬ᶜ ((g A))) ∨ᶜ (¬ᶜ ((f A))) ∨ᶜ ⊥)
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t9 t8;
    };
    have t9_t8_h7 : π̇ (((¬ᶜ ((g A))) ∨ᶜ (¬ᶜ ((f A))) ∨ᶜ ⊥) ⟇ ▩) {
        apply resolutionᵣ _ _ _ t9_t8 h7;
    };
    refine t9_t8_h7;
};
have t11 : π̇ ((¬ᶜ ((g A)))  ⟇ (¬ᶜ ((f A))) ⟇ ▩) {
    apply π̇ₗ t10;
};
have t12 : π̇ ▩ {
    have t11_t5 : π̇ ((¬ᶜ ((g A))) ⟇ ▩) {
        have t11' : (π̇ ((¬ᶜ ((g A)))  ⟇ (¬ᶜ ((f A))) ⟇ ▩) → π̇ ((¬ᶜ ((f A)))  ⟇ (¬ᶜ ((g A))) ⟇ ▩)) {
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