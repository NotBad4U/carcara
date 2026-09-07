// Quantifier and binder rules: Hilbert choice, instantiation, skolemisation
// and the bind_* congruences. Opened only when the logic is not quantifier-free,
// which keeps the choice axiom out of quantifier-free proofs.
require open lambdapi.core;
symbol ϵ  [a]: (τ a → Prop) → τ a; notation ϵ quantifier;
constant symbol ϵᵢ [a] x (p: τ a → Prop) : π (p x) → π (p (ϵ p));
constant symbol ϵ_det [a p q]: Π (x: τ a), π ((p x) ⇔ (q x)) → π (ϵ p = ϵ q);
opaque symbol ϵ_to_∃ [a] p: π ((`∃ (x : τ a),  p x) = p (`ϵ (x : τ a), p x)) ≔
begin
  assume a p;
  apply prop_ext;
  apply ∧ᵢ
  {
    assume H;
    apply ∃ₑ H;
    assume x H1;
    apply ϵᵢ x (λ u, (p u)) H1;
  }
  {
    refine (∧ₑ₂ (@contrapos (p (`ϵ x, p x) ) (`∃ x, p x))) _;
    assume H;
    have H1: π (`∀ x, ¬ p x) { apply ((∧ₑ₁ (nex_forall p)) H) };
    refine H1 (`ϵ x, p x);
  }
end;
opaque symbol ϵ_to_∀ [a] p: π ((`∀ (x : τ a), p x) = p (`ϵ (x : τ a), (¬ p x))) ≔
begin
  assume a p;
  apply prop_ext;
  apply ∧ᵢ
  {
    assume H;
    apply H (`ϵ x, ¬ (p x)) 
  }
  {
    simplify;
    refine (∧ₑ₂ (@contrapos (p (`ϵ x, ¬ (p x)) ) (`∀ x, p x))) _;
    assume H;
    
    have H1: π (`∃ x, ¬ p x) { refine ((∧ₑ₁ (nforall_ex p)) H) };
    apply ∃ₑ H1;
    assume x Hnpx;
    refine ϵᵢ x (λ u, ¬ (p u)) Hnpx;
  }
end;
opaque symbol ϵ_equiv_∃' [a p] : π ((`∃ (x: τ a), p x) = (p (`ϵ x, p x))) ≔
begin
  assume a p;
  apply prop_ext;
  apply ∧ᵢ
  {
    
    assume Hexist;
    apply ∃ₑ Hexist;
    assume x Hpx;
    apply ϵᵢ x (λ u, p u);
    apply Hpx
  }
  {
    
    assume Heps;
    apply ∃ᵢ (`ϵ x, p x);
    apply Heps
  }
end;
opaque symbol ϵ_equiv_∃ [a p] : π ((`∃ x: τ a, p x) ⇔ (p (`ϵ x, p x))) ≔
begin
  assume a p;
  apply ∧ᵢ
  {
    
    assume Hexist;
    apply ∃ₑ Hexist;
    assume x Hpx;
    apply ϵᵢ x (λ u, p u);
    apply Hpx
  }
  {
    
    assume Heps;
    apply ∃ᵢ (`ϵ x, p x);
    apply Heps
  }
end;
opaque symbol forall_inst1 [a] p (x: τ a) : π (¬ (`∀ x', p x') ∨ (p x)) ≔
begin
 assume a p x;
 rewrite imp_eq_or;
 assume H;
 apply H
end;
opaque symbol forall_inst2 [a] p (x y: τ a) : π (¬ (`∀ a, `∀ b, p a b) ∨ (p x y)) ≔
begin
  assume a p x y;
  rewrite imp_eq_or;
  assume H;
  apply H
 end;
opaque symbol forall_inst3 [a] [p] (x y z: τ a) : π ((¬ (`∀ a, `∀ b, `∀ c, p a b c)) ∨ ((p x y z) ∨ ⊥)) ≔
begin
  assume a p x y z;
  apply imply_to_or;
  assume H;
  rewrite or_identity_r;
  apply H
end;
opaque symbol bind_∃ [a p q]: (Π x, π (p x = q x))  → π ((`∃ (x: τ a), p x) = (`∃ (x: τ a), q x)) ≔
begin
  assume a p q H;
  apply prop_ext;
  apply ∧ᵢ
  {
    
    assume H1;
    apply ∃ₑ H1;
    assume x Hpx;
    apply ∃ᵢ x;
    simplify;
    rewrite left (H x);
    apply Hpx;
  }
  {
    
    assume H1;
    apply ∃ₑ H1;
    assume x Hqx;
    apply ∃ᵢ x;
    simplify;
    rewrite (H x);
    apply Hqx;
  };
end;
opaque symbol bind_∀ [a p q]: (Π (x: τ a), π (p x = q x))  → π ((`∀ (x: τ a), p x) = (`∀ (x: τ a), q x)) ≔
begin
  assume a p q H;
  apply prop_ext;
  apply ∧ᵢ
  {
    
    assume H1;
    assume x;
    have Hpx: π (p x) { apply H1; };
    rewrite left (H x);
    apply Hpx;
  }
  {
    
    assume H1;
    assume x;
    have Hqx: π (q x) { apply H1 };
    rewrite (H x);
    apply Hqx;
  };
end;
opaque symbol bind_∀' [a p q]: (Π (x: τ a), Π (y: τ a), π (x = y) → π (p x = q y))  → π ((`∀ (x: τ a), p x) = (`∀ (y: τ a), q y)) ≔
begin
  assume a p q;
  assume H;
  apply prop_ext;
  apply ∧ᵢ
  {
    
    assume H1;
    assume x;
    have Hpx: π (p x) { apply H1; };
    rewrite left H x x (eq_refl x);
    apply Hpx
  }
  {
    
    assume H1;
    assume x;
    have Hqx: π (q x) { apply H1 };
    rewrite H x x (eq_refl x);
    apply Hqx;
  };
end;
opaque symbol sko_forall [a p q]: (Π (x: τ a), π (x = `ϵ (y: τ a), ¬ (p y)) → π (p x = q))  → π ((`∀ (x: τ a), p x) = q) ≔
begin
  assume a p q H;
  apply prop_ext;
  apply ∧ᵢ
  {
    refine  (∧ₑ₂ (@contrapos (`∀ x, p x) q)) _;
    assume Hnq;
    rewrite .[x in ¬ x]  (ϵ_to_∀ p);
    have H1:  π (p (`ϵ x, ¬ (p x)) = q) { apply H; reflexivity };
    rewrite H1;
    refine Hnq
  }
  {
    rewrite .[x in _ ⇒ x]  (ϵ_to_∀ p);
    
    assume Hq;
    have H1:  π (p (`ϵ y, ¬ (p y)) = q) { apply H; reflexivity };
    rewrite H1;
    apply Hq
  }
end;

// Inductive t A : nat -> Type :=
//   |nil : t A 0
//   |cons : forall (h:A) (n:nat), t A n -> t A (S n).
