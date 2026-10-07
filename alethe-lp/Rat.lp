/*
  ℚ as a quotient type (Stdlib.Quotient). A fraction is a pair `n ‚ d` of a
  numerator n : ℤ and a denominator d : ℙ, and two fractions are the same
  rational when they cross-multiply to the same integer:
    n₁/d₁ = n₂/d₂   iff   n₁ * d₂ = n₂ * d₁.
*/

require open Stdlib.Nat Stdlib.Z Stdlib.Prop Stdlib.Prod Stdlib.Quotient;

opaque symbol *_swap a b c d : π ((a * b) * (c * d) = (a * c) * (b * d)) ≔
begin
  assume a b c d;
  rewrite *_assoc a b (c * d);
  rewrite left *_assoc b c d;
  rewrite *_com b c;
  rewrite *_assoc c b d;
  rewrite left *_assoc a c (b * d);
  reflexivity
end;


symbol ≅ : τ (int × pos) → τ (int × pos) → Prop; notation ≅ infix 10;
rule $x ≅ $y ↪ ($x ₁) * Zpos ($y ₂) = ($y ₁) * Zpos ($x ₂);

opaque symbol ≅_refl x : π (x ≅ x) ≔
begin
  assume x; reflexivity
end;

opaque symbol ≅_sym x y : π (x ≅ y) → π (y ≅ x) ≔
begin
  assume x y h; symmetry; refine h
end;

opaque symbol ≅_trans x y z : π (x ≅ y) → π (y ≅ z) → π (x ≅ z) ≔
begin
  induction; assume a p; induction; assume b q; induction; assume c r;
  change π (a * Zpos q = b * Zpos p) → π (b * Zpos r = c * Zpos q) → π (a * Zpos r = c * Zpos p);
  assume hab hbc;
  refine *_reg_r (a * Zpos r) (c * Zpos p) (Zpos q) (Zpos≠Z0 q) _;
  rewrite *_assoc a (Zpos r) (Zpos q);
  rewrite *_com (Zpos r) (Zpos q);
  rewrite left *_assoc a (Zpos q) (Zpos r);
  rewrite hab;
  rewrite *_assoc b (Zpos p) (Zpos r);
  rewrite *_com (Zpos p) (Zpos r);
  rewrite left *_assoc b (Zpos r) (Zpos p);
  rewrite hbc;
  rewrite *_assoc c (Zpos q) (Zpos p);
  rewrite *_assoc c (Zpos p) (Zpos q);
  rewrite *_com (Zpos q) (Zpos p);
  reflexivity
end;

symbol rat : Set ≔ (int × pos) ⫽ (≅);
symbol ℚ : TYPE ≔ τ rat;

// The rational n/d, for a positive denominator d.
symbol / (n : ℤ) (d : ℙ) : ℚ ≔ class (≅) (n ‚ d); notation / infix right 30;

symbol 0⫽1 : ℚ ≔ 0 / H;
symbol 1⫽1 : ℚ ≔ 1 / H;

symbol inj_z (x : ℤ) : ℚ ≔ x / H;

coerce_rule coerce ℤ (Quot (≅)) $x ↪ inj_z $x;
 

/* ------------------------------------------------------------------------
   Operations on ℚ
   ------------------------------------------------------------------------ */

symbol 𝕢+ : ℚ → ℚ → ℚ; notation 𝕢+ infix right 20;
rule (cl $x) 𝕢+ (cl $y) ↪ class (≅) ((($x ₁) * Zpos ($y ₂) + ($y ₁) * Zpos ($x ₂)) ‚ mul ($x ₂) ($y ₂));

symbol *𝕢 : ℚ → ℚ → ℚ; notation *𝕢 infix right 22;
rule (cl $x) *𝕢 (cl $y) ↪ class (≅) ((($x ₁) * ($y ₁)) ‚ mul ($x ₂) ($y ₂));

symbol —𝕢 : ℚ → ℚ; notation —𝕢 prefix 24;
rule —𝕢 (cl $x) ↪ class (≅) ((— ($x ₁)) ‚ ($x ₂));

symbol 𝕢- (x y : ℚ) : ℚ ≔ x 𝕢+ —𝕢 y; notation 𝕢- infix left 20;

symbol 𝕢≐ : ℚ → ℚ → Comp; notation 𝕢≐ infix 10;
rule (cl $x) 𝕢≐ (cl $y) ↪ ($x ₁) * Zpos ($y ₂) ≐ ($y ₁) * Zpos ($x ₂);

opaque symbol 𝕢+_compat x x' : π (x ≅ x') → Π y y', π (y ≅ y') →
  π (cl x 𝕢+ cl y = cl x' 𝕢+ cl y') ≔
begin
  induction; assume a p; induction; assume a' p' rx;
  induction; assume b q; induction; assume b' q' ry;
  have hx : π (a * Zpos p' = a' * Zpos p) { refine rx };
  have hy : π (b * Zpos q' = b' * Zpos q) { refine ry };
  apply sound;
  change π ((a * Zpos q + b * Zpos p) * (Zpos p' * Zpos q')
            = (a' * Zpos q' + b' * Zpos p') * (Zpos p * Zpos q));
  rewrite *_distr_r (a * Zpos q) (b * Zpos p) (Zpos p' * Zpos q');
  rewrite *_distr_r (a' * Zpos q') (b' * Zpos p') (Zpos p * Zpos q);
  rewrite *_swap a (Zpos q) (Zpos p') (Zpos q');
  rewrite *_com (Zpos p') (Zpos q');
  rewrite *_swap b (Zpos p) (Zpos q') (Zpos p');
  rewrite *_swap a' (Zpos q') (Zpos p) (Zpos q);
  rewrite *_com (Zpos q') (Zpos q);
  rewrite *_com (Zpos p) (Zpos q);
  rewrite *_swap b' (Zpos p') (Zpos q) (Zpos p);
  rewrite *_com (Zpos p') (Zpos p);
  rewrite hx; rewrite hy; reflexivity
end;

opaque symbol *𝕢_compat x x' : π (x ≅ x') → Π y y', π (y ≅ y') →
  π (cl x *𝕢 cl y = cl x' *𝕢 cl y') ≔
begin
  induction; assume a p; induction; assume a' p' rx;
  induction; assume b q; induction; assume b' q' ry;
  have hx : π (a * Zpos p' = a' * Zpos p) { refine rx };
  have hy : π (b * Zpos q' = b' * Zpos q) { refine ry };
  apply sound;
  change π ((a * b) * (Zpos p' * Zpos q') = (a' * b') * (Zpos p * Zpos q));
  rewrite *_swap a b (Zpos p') (Zpos q');
  rewrite *_swap a' b' (Zpos p) (Zpos q);
  rewrite hx; rewrite hy; reflexivity
end;

opaque symbol —𝕢_compat x x' : π (x ≅ x') → π (—𝕢 cl x = —𝕢 cl x') ≔
begin
  induction; assume a p; induction; assume a' p' rx;
  have hx : π (a * Zpos p' = a' * Zpos p) { refine rx };
  apply sound;
  change π ((— a) * Zpos p' = (— a') * Zpos p);
  rewrite left neg_mul_l a (Zpos p');
  rewrite left neg_mul_l a' (Zpos p);
  rewrite hx; reflexivity
end;

opaque symbol 𝕢≐_compat x x' : π (x ≅ x') → Π y y', π (y ≅ y') →
  π ((cl x 𝕢≐ cl y) = (cl x' 𝕢≐ cl y')) ≔
begin
  induction; assume a p; induction; assume a' p' rx;
  induction; assume b q; induction; assume b' q' ry;
  have hx : π (a * Zpos p' = a' * Zpos p) { refine rx };
  have hy : π (b * Zpos q' = b' * Zpos q) { refine ry };
  change π ((a * Zpos q ≐ b * Zpos p) = (a' * Zpos q' ≐ b' * Zpos p'));
  rewrite ≐_compat_mul (a * Zpos q) (b * Zpos p) (mul p' q');
  rewrite ≐_compat_mul (a' * Zpos q') (b' * Zpos p') (mul p q);
  change π (((a * Zpos q) * (Zpos p' * Zpos q') ≐ (b * Zpos p) * (Zpos p' * Zpos q'))
          = ((a' * Zpos q') * (Zpos p * Zpos q) ≐ (b' * Zpos p') * (Zpos p * Zpos q)));
  rewrite *_swap a (Zpos q) (Zpos p') (Zpos q');
  rewrite *_com (Zpos p') (Zpos q');
  rewrite *_swap b (Zpos p) (Zpos q') (Zpos p');
  rewrite *_swap a' (Zpos q') (Zpos p) (Zpos q);
  rewrite *_com (Zpos q') (Zpos q);
  rewrite *_com (Zpos p) (Zpos q);
  rewrite *_swap b' (Zpos p') (Zpos q) (Zpos p);
  rewrite *_com (Zpos p') (Zpos p);
  rewrite hx; rewrite hy; reflexivity
end;

opaque symbol 𝕢+_lift2 (x y : τ rat) :
  π (x 𝕢+ y = @lift2 _ (≅) ≅_refl rat
                (λ x y, class (≅) (((x ₁) * Zpos (y ₂) + (y ₁) * Zpos (x ₂)) ‚ mul (x ₂) (y ₂)))
                𝕢+_compat x y) ≔
begin
  induction; assume x; induction; assume y; reflexivity
end;

opaque symbol *𝕢_lift2 (x y : τ rat) :
  π (x *𝕢 y = @lift2 _ (≅) ≅_refl rat
                (λ x y, class (≅) (((x ₁) * (y ₁)) ‚ mul (x ₂) (y ₂)))
                *𝕢_compat x y) ≔
begin
  induction; assume x; induction; assume y; reflexivity
end;

opaque symbol —𝕢_lift (x : τ rat) :
  π (—𝕢 x = @lift _ (≅) rat (λ x, class (≅) ((— (x ₁)) ‚ (x ₂))) —𝕢_compat x) ≔
begin
  induction; assume x; reflexivity
end;

opaque symbol 𝕢≐_lift2 (x y : τ rat) :
  π ((x 𝕢≐ y) = @lift2 _ (≅) ≅_refl comp
                  (λ x y, (x ₁) * Zpos (y ₂) ≐ (y ₁) * Zpos (x ₂))
                  𝕢≐_compat x y) ≔
begin
  induction; assume x; induction; assume y; reflexivity
end;

// Ring laws

opaque symbol div_0_num d : π (0 / d = 0⫽1) ≔
begin
  assume d; apply sound; reflexivity
end;

opaque symbol 𝕢+_com (x y : τ rat) : π (x 𝕢+ y = y 𝕢+ x) ≔
begin
  induction; induction; assume a p; induction; induction; assume b q;
  change π (class (≅) ((a * Zpos q + b * Zpos p) ‚ mul p q)
            = class (≅) ((b * Zpos p + a * Zpos q) ‚ mul q p));
  rewrite +_com (a * Zpos q) (b * Zpos p);
  rewrite mul_com p q;
  reflexivity
end;

opaque symbol 𝕢+_assoc (x y z : τ rat) : π ((x 𝕢+ y) 𝕢+ z = x 𝕢+ (y 𝕢+ z)) ≔
begin
  induction; induction; assume a p; induction; induction; assume b q;
  induction; induction; assume c r;
  change π (class (≅) (((a * Zpos q + b * Zpos p) * Zpos r + c * (Zpos p * Zpos q)) ‚ mul (mul p q) r)
            = class (≅) ((a * (Zpos q * Zpos r) + (b * Zpos r + c * Zpos q) * Zpos p) ‚ mul p (mul q r)));
  rewrite mul_assoc p q r;
  rewrite *_distr_r (a * Zpos q) (b * Zpos p) (Zpos r);
  rewrite +_assoc ((a * Zpos q) * Zpos r) ((b * Zpos p) * Zpos r) (c * (Zpos p * Zpos q));
  rewrite *_distr_r (b * Zpos r) (c * Zpos q) (Zpos p);
  rewrite *_assoc a (Zpos q) (Zpos r);
  rewrite *_assoc b (Zpos p) (Zpos r);
  rewrite *_assoc b (Zpos r) (Zpos p);
  rewrite *_com (Zpos r) (Zpos p);
  rewrite *_assoc c (Zpos q) (Zpos p);
  rewrite *_com (Zpos q) (Zpos p);
  reflexivity
end;

opaque symbol 𝕢+_neutral_l (x : τ rat) : π (0⫽1 𝕢+ x = x) ≔
begin
  induction; induction; assume a p;
  change π (class (≅) ((a * Zpos H) ‚ p) = class (≅) (a ‚ p));
  rewrite *_neutral a; reflexivity
end;

opaque symbol 𝕢+_neutral_r (x : τ rat) : π (x 𝕢+ 0⫽1 = x) ≔
begin
  assume x; rewrite 𝕢+_com x 0⫽1; refine 𝕢+_neutral_l x
end;

opaque symbol 𝕢+_opp_r (x : τ rat) : π (x 𝕢+ (—𝕢 x) = 0⫽1) ≔
begin
  induction; induction; assume a p; apply sound;
  change π ((a * Zpos p + (— a) * Zpos p) * Zpos H = Z0);
  rewrite left neg_mul_l a (Zpos p);
  rewrite -_same (a * Zpos p);
  reflexivity
end;

opaque symbol *𝕢_com (x y : τ rat) : π (x *𝕢 y = y *𝕢 x) ≔
begin
  induction; induction; assume a p; induction; induction; assume b q;
  change π (class (≅) ((a * b) ‚ mul p q) = class (≅) ((b * a) ‚ mul q p));
  rewrite *_com a b; rewrite mul_com p q; reflexivity
end;

opaque symbol *𝕢_assoc (x y z : τ rat) : π ((x *𝕢 y) *𝕢 z = x *𝕢 (y *𝕢 z)) ≔
begin
  induction; induction; assume a p; induction; induction; assume b q;
  induction; induction; assume c r;
  change π (class (≅) (((a * b) * c) ‚ mul (mul p q) r)
            = class (≅) ((a * (b * c)) ‚ mul p (mul q r)));
  rewrite *_assoc a b c; rewrite mul_assoc p q r; reflexivity
end;

opaque symbol *𝕢_neutral_r (x : τ rat) : π (x *𝕢 1⫽1 = x) ≔
begin
  induction; induction; assume a p;
  change π (class (≅) ((a * Zpos H) ‚ mul p H) = class (≅) (a ‚ p));
  rewrite *_neutral a; rewrite mul_H_right p; reflexivity
end;

opaque symbol *𝕢_neutral_l (x : τ rat) : π (1⫽1 *𝕢 x = x) ≔
begin
  assume x; rewrite *𝕢_com 1⫽1 x; refine *𝕢_neutral_r x
end;

opaque symbol distr*𝕢𝕢+ (x y z : τ rat) : π (x *𝕢 (y 𝕢+ z) = x *𝕢 y 𝕢+ x *𝕢 z) ≔
begin
  induction; induction; assume a p; induction; induction; assume b q;
  induction; induction; assume c r;
  apply sound;
  change π ((a * (b * Zpos r + c * Zpos q)) * ((Zpos p * Zpos q) * (Zpos p * Zpos r))
            = ((a * b) * (Zpos p * Zpos r) + (a * c) * (Zpos p * Zpos q)) * (Zpos p * (Zpos q * Zpos r)));
  rewrite *_com (a * b) (Zpos p * Zpos r);
  rewrite *_assoc (Zpos p) (Zpos r) (a * b);
  rewrite *_com (Zpos r) (a * b);
  rewrite *_assoc a b (Zpos r);
  rewrite *_com (a * c) (Zpos p * Zpos q);
  rewrite *_assoc (Zpos p) (Zpos q) (a * c);
  rewrite *_com (Zpos q) (a * c);
  rewrite *_assoc a c (Zpos q);
  rewrite left *_distr_l (Zpos p) (a * (b * Zpos r)) (a * (c * Zpos q));
  rewrite left *_distr_l a (b * Zpos r) (c * Zpos q);
  rewrite *_swap (Zpos p) (Zpos q) (Zpos p) (Zpos r);
  rewrite *_assoc (Zpos p) (Zpos p) (Zpos q * Zpos r);
  rewrite left *_assoc (a * (b * Zpos r + c * Zpos q)) (Zpos p) (Zpos p * (Zpos q * Zpos r));
  rewrite *_com (a * (b * Zpos r + c * Zpos q)) (Zpos p);
  reflexivity
end;
