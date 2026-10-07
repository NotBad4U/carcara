require open alethe.rat;

constant symbol real : Set;

symbol ≤ᵣ : τ real → τ real → Prop;
notation ≤ᵣ infix 10;

// The other comparisons, from ≤ᵣ (total: see le_total).
symbol ≥ᵣ (x y : τ real) : Prop ≔ y ≤ᵣ x;
notation ≥ᵣ infix 10;

symbol <ᵣ (x y : τ real) : Prop ≔ ¬ (y ≤ᵣ x);
notation <ᵣ infix 10;

symbol >ᵣ (x y : τ real) : Prop ≔ y <ᵣ x;
notation >ᵣ infix 10;

// supremum of a (nonempty, bounded) real set.
symbol sup : (τ real → Prop) → τ real;

// ＋ is the fullwidth plus sign (U+FF0B): `+` followed by a lowercase letter
// is read by the lexer as a debug flag.
symbol ＋ᵣ : τ real → τ real → τ real;
notation ＋ᵣ infix right 20;

symbol zero : τ real;

symbol —ᵣ : τ real → τ real;
notation —ᵣ prefix 24;

symbol *ᵣ : τ real → τ real → τ real;
notation *ᵣ infix right 22;

symbol one : τ real;

symbol ⁻¹ : τ real → τ real;
notation ⁻¹ postfix 26;

// Subtraction; − is the minus sign (U+2212), not the ASCII hyphen.
symbol −ᵣ x y ≔ x ＋ᵣ —ᵣ y;
notation −ᵣ infix left 20;

// Equality as the preorder equivalence
symbol eq (x y : τ real) : Prop ≔ x ≤ᵣ y ∧ y ≤ᵣ x;

// Set of upper bounds of a real set.
symbol ↑ᵣ (E : τ real → Prop) : τ real → Prop ≔ λ z, `∀ y, E y ⇒ y ≤ᵣ z;
notation ↑ᵣ prefix 24;

// Downward closure of E: (↓ᵣ E) x ⟺ x ≤ᵣ y for some y such that E y.
symbol ↓ᵣ (E : τ real → Prop) : τ real → Prop ≔ λ x, `∃ y, E y ∧ x ≤ᵣ y;
notation ↓ᵣ prefix 24;

// === Real set supremum existence condition =====

symbol nonempty (E : τ real → Prop) : Prop ≔ `∃ x, E x;

symbol has_ub (E : τ real → Prop) : Prop ≔ nonempty (↑ᵣ E);

symbol has_sup (E : τ real → Prop) : Prop ≔ nonempty E ∧ has_ub E;


// =====

// the complete-ordered-field axioms

// ≤ᵣ is a preorder.
symbol le_reflexive (x : τ real) : π (x ≤ᵣ x);
symbol le_transitive (x y z : τ real) : π (x ≤ᵣ y ⇒ y ≤ᵣ z ⇒ x ≤ᵣ z);

// sup is the least upper bound.  sup_total is the constructive minimality
// axiom that (in Rocq) forces the excluded middle and totality of the order.
symbol sup_upper_bound (E : τ real → Prop) : π (has_sup E ⇒ (↑ᵣ E) (sup E));

symbol sup_total (E : τ real → Prop) (x : τ real) :
  π (has_sup E ⇒ ((↓ᵣ E) x ∨ sup E ≤ᵣ x));

symbol add_monotone (x y z : τ real) : π (y ≤ᵣ z) → π (x ＋ᵣ y ≤ᵣ x ＋ᵣ z);

symbol add_commutative (x y : τ real) : π (eq (x ＋ᵣ y) (y ＋ᵣ x));

symbol add_associative (x y z : τ real) : π (eq (x ＋ᵣ (y ＋ᵣ z)) ((x ＋ᵣ y) ＋ᵣ z));

symbol add_zero_left (x : τ real) : π (eq (zero ＋ᵣ x) x);

symbol add_opposite_right (x : τ real) : π (eq (x ＋ᵣ —ᵣ x) zero);

symbol mul_monotone (x y z : τ real) :
  π (zero ≤ᵣ x ⇒ y ≤ᵣ z ⇒ x *ᵣ y ≤ᵣ x *ᵣ z);

symbol mul_commutative (x y : τ real) : π (eq (x *ᵣ y) (y *ᵣ x));

symbol mul_associative (x y z : τ real) :
  π (eq (x *ᵣ (y *ᵣ z)) ((x *ᵣ y) *ᵣ z));

symbol mul_distributive_right (x y z : τ real) :
  π (eq (x *ᵣ (y ＋ᵣ z)) ((x *ᵣ y) ＋ᵣ (x *ᵣ z)));

symbol mul_one_left (x : τ real) : π (eq (one *ᵣ x) x);

symbol mul_inverse_right (x : τ real) :
  π (¬ (eq x zero) ⇒ eq (x *ᵣ x ⁻¹) one);

symbol one_nonzero : π (¬ (eq one zero));

// Antisymmetry of ≤ᵣ with respect to Leibniz equality.  This is the only
// axiom relating the setoid equality `eq` to `=`: it is not derivable from
// the axioms above, which constrain the structure only up to `eq` (a model
// that duplicates each real into two `eq`-equivalent copies satisfies all
// of them), but it holds in the standard model ℝ (cf. Rocq's Rle_antisym).
// https://rocq-prover.org/doc/V9.0.0/stdlib/Stdlib.Reals.RIneq.html#Rle_antisym
symbol le_antisymmetric (x y : τ real) : π (x ≤ᵣ y ⇒ y ≤ᵣ x ⇒ x = y);

// √2 : the square root of two

symbol two : τ real ≔ one ＋ᵣ one;

symbol below_root2 : τ real → Prop ≔ λ x, zero ≤ᵣ x ∧ x *ᵣ x ≤ᵣ two;

// √2 =  sup { x | 0 ≤ x ∧ x·x ≤ 2 }
symbol √2 : τ real ≔ sup below_root2;

// ---------------------------------------------------------------------------
// Specification of √2.
//
// E is nonempty (0 ∈ E) and bounded above (by 2), so `has_sup E` holds and the
// sup axioms apply.  From them the defining properties of √2 follow:
//     0 ≤ √2      and      √2 · √2 = 2.
// These are *theorems* about the definition above (not new axioms); their
// proofs are the usual completeness argument (squeeze √2·√2 between the two
// `sup` bounds), built on the ordered-field lemmas.  Stated here as the spec.
// ---------------------------------------------------------------------------
// ===========================================================================
// A. order / eq combinators   (fully explicit arguments)
// ===========================================================================

symbol le_refl x : π (x ≤ᵣ x) ≔ le_reflexive x;

symbol le_tr x y z : π (x ≤ᵣ y) → π (y ≤ᵣ z) → π (x ≤ᵣ z) ≔
  λ h1 h2, le_transitive x y z h1 h2;

symbol eq_le x y : π (eq x y) → π (x ≤ᵣ y) ≔ λ h, ∧ₑ₁ h;
symbol eq_ge x y : π (eq x y) → π (y ≤ᵣ x) ≔ λ h, ∧ₑ₂ h;

symbol eq_refl' x : π (eq x x) ≔ ∧ᵢ (le_refl x) (le_refl x);

symbol eq_sym' x y : π (eq x y) → π (eq y x) ≔ λ h, ∧ᵢ (∧ₑ₂ h) (∧ₑ₁ h);

symbol eq_tr x y z : π (eq x y) → π (eq y z) → π (eq x z) ≔
  λ h1 h2, ∧ᵢ (le_transitive x y z (∧ₑ₁ h1) (∧ₑ₁ h2))
              (le_transitive z y x (∧ₑ₂ h2) (∧ₑ₂ h1));

symbol le_eq_tr x y z : π (x ≤ᵣ y) → π (eq y z) → π (x ≤ᵣ z) ≔
  λ h e, le_transitive x y z h (∧ₑ₁ e);
symbol eq_le_tr x y z : π (eq x y) → π (y ≤ᵣ z) → π (x ≤ᵣ z) ≔
  λ e h, le_transitive x y z (∧ₑ₁ e) h;

// `eq` coincides with Leibniz equality: `le_antisymmetric` gives the forward
// direction; the converse is transport along `ind_eq` (no axiom needed).
symbol leibniz_of_eq x y : π (eq x y) → π (x = y) ≔
  λ h, le_antisymmetric x y (∧ₑ₁ h) (∧ₑ₂ h);

symbol eq_of_leibniz x y : π (x = y) → π (eq x y) ≔
  λ h, ind_eq h (λ z, eq z y) (eq_refl' y);

symbol eq_iff_leibniz x y : π (eq x y ⇔ x = y) ≔
  ∧ᵢ (leibniz_of_eq x y) (eq_of_leibniz x y);

// ===========================================================================
// B. The field laws as Leibniz equalities
//
// The axioms constrain the reals up to `eq`; by `eq_iff_leibniz` they also
// hold for `=`, which `rewrite` can use. From here on, lemmas are stated and
// proved with `=`.
// ===========================================================================

opaque symbol add_com x y : π (x ＋ᵣ y = y ＋ᵣ x) ≔
begin
  assume x y; refine leibniz_of_eq _ _ (add_commutative x y)
end;

opaque symbol add_assoc x y z : π ((x ＋ᵣ y) ＋ᵣ z = x ＋ᵣ (y ＋ᵣ z)) ≔
begin
  assume x y z; symmetry; refine leibniz_of_eq _ _ (add_associative x y z)
end;

opaque symbol add_zero_l x : π (zero ＋ᵣ x = x) ≔
begin
  assume x; refine leibniz_of_eq _ _ (add_zero_left x)
end;

opaque symbol add_opp_r x : π (x ＋ᵣ —ᵣ x = zero) ≔
begin
  assume x; refine leibniz_of_eq _ _ (add_opposite_right x)
end;

opaque symbol mul_com x y : π (x *ᵣ y = y *ᵣ x) ≔
begin
  assume x y; refine leibniz_of_eq _ _ (mul_commutative x y)
end;

opaque symbol mul_assoc x y z : π ((x *ᵣ y) *ᵣ z = x *ᵣ (y *ᵣ z)) ≔
begin
  assume x y z; symmetry; refine leibniz_of_eq _ _ (mul_associative x y z)
end;

opaque symbol mul_distr_l x y z : π (x *ᵣ (y ＋ᵣ z) = (x *ᵣ y) ＋ᵣ (x *ᵣ z)) ≔
begin
  assume x y z; refine leibniz_of_eq _ _ (mul_distributive_right x y z)
end;

opaque symbol mul_one_l x : π (one *ᵣ x = x) ≔
begin
  assume x; refine leibniz_of_eq _ _ (mul_one_left x)
end;

opaque symbol mul_inv_r x : π (x ≠ zero) → π (x *ᵣ x ⁻¹ = one) ≔
begin
  assume x h; refine leibniz_of_eq _ _ (mul_inverse_right x _);
  assume e; refine h (leibniz_of_eq x zero e)
end;

opaque symbol one≠zero : π (one ≠ zero) ≔
begin
  assume h; refine one_nonzero (eq_of_leibniz one zero h)
end;

// ===========================================================================
// Ring lemmas
// ===========================================================================

opaque symbol add_zero_r x : π (x ＋ᵣ zero = x) ≔
begin
  assume x; rewrite add_com x zero; refine add_zero_l x
end;

opaque symbol add_opp_l x : π ((—ᵣ x) ＋ᵣ x = zero) ≔
begin
  assume x; rewrite add_com (—ᵣ x) x; refine add_opp_r x
end;

opaque symbol add_opp_cancel_l z x : π ((—ᵣ z) ＋ᵣ (z ＋ᵣ x) = x) ≔
begin
  assume z x; rewrite left add_assoc (—ᵣ z) z x; rewrite add_opp_l z; refine add_zero_l x
end;

opaque symbol add_cancel_l z x y : π (z ＋ᵣ x = z ＋ᵣ y) → π (x = y) ≔
begin
  assume z x y h;
  rewrite left add_opp_cancel_l z x; rewrite left add_opp_cancel_l z y;
  rewrite h; reflexivity
end;

opaque symbol add_sub_cancel x y : π (x ＋ᵣ (y −ᵣ x) = y) ≔
begin
  assume x y; simplify;
  rewrite add_com y (—ᵣ x); rewrite left add_assoc x (—ᵣ x) y;
  rewrite add_opp_r x; refine add_zero_l y
end;

opaque symbol sub_undo a b : π ((b −ᵣ a) ＋ᵣ a = b) ≔
begin
  assume a b; simplify; rewrite add_assoc b (—ᵣ a) a; rewrite add_opp_l a; refine add_zero_r b
end;

opaque symbol eq_opp_of_add_zero a b : π (a ＋ᵣ b = zero) → π (a = —ᵣ b) ≔
begin
  assume a b h;
  rewrite left add_zero_r a; rewrite left add_opp_r b; rewrite left add_assoc a b (—ᵣ b);
  rewrite h; refine add_zero_l (—ᵣ b)
end;

opaque symbol opp_opp x : π (—ᵣ (—ᵣ x) = x) ≔
begin
  assume x; symmetry; refine eq_opp_of_add_zero x (—ᵣ x) (add_opp_r x)
end;

opaque symbol opp_zero : π (—ᵣ zero = zero) ≔
begin
  symmetry; refine eq_opp_of_add_zero zero zero (add_zero_l zero)
end;

opaque symbol mul_one_r x : π (x *ᵣ one = x) ≔
begin
  assume x; rewrite mul_com x one; refine mul_one_l x
end;

opaque symbol mul_distr_r x y z : π ((x ＋ᵣ y) *ᵣ z = (x *ᵣ z) ＋ᵣ (y *ᵣ z)) ≔
begin
  assume x y z;
  rewrite mul_com (x ＋ᵣ y) z; rewrite mul_com x z; rewrite mul_com y z;
  refine mul_distr_l z x y
end;

opaque symbol mul_zero_r x : π (x *ᵣ zero = zero) ≔
begin
  assume x;
  refine add_cancel_l (x *ᵣ zero) (x *ᵣ zero) zero _;
  rewrite left mul_distr_l x zero zero; rewrite add_zero_l zero;
  rewrite add_zero_r (x *ᵣ zero); reflexivity
end;

opaque symbol mul_zero_l x : π (zero *ᵣ x = zero) ≔
begin
  assume x; rewrite mul_com zero x; refine mul_zero_r x
end;

opaque symbol neg_mul a b : π ((—ᵣ a) *ᵣ b = —ᵣ (a *ᵣ b)) ≔
begin
  assume a b;
  refine eq_opp_of_add_zero ((—ᵣ a) *ᵣ b) (a *ᵣ b) _;
  rewrite left mul_distr_r (—ᵣ a) a b; rewrite add_opp_l a; refine mul_zero_l b
end;

opaque symbol mul_neg_r a b : π (a *ᵣ —ᵣ b = —ᵣ (a *ᵣ b)) ≔
begin
  assume a b; rewrite mul_com a (—ᵣ b); rewrite neg_mul b a; rewrite mul_com b a; reflexivity
end;

opaque symbol mul_opp_opp a b : π ((—ᵣ a) *ᵣ (—ᵣ b) = a *ᵣ b) ≔
begin
  assume a b; rewrite neg_mul a (—ᵣ b); rewrite mul_neg_r a b; refine opp_opp (a *ᵣ b)
end;

opaque symbol two_mul x : π (two *ᵣ x = x ＋ᵣ x) ≔
begin
  assume x; simplify two; rewrite mul_distr_r one one x; rewrite mul_one_l x; reflexivity
end;

opaque symbol mul_inv_cancel D x : π (D ≠ zero) → π (D *ᵣ (x *ᵣ D ⁻¹) = x) ≔
begin
  assume D x h;
  rewrite mul_com x (D ⁻¹); rewrite left mul_assoc D (D ⁻¹) x;
  rewrite mul_inv_r D h; refine mul_one_l x
end;

opaque symbol add4 a b c d : π ((a ＋ᵣ b) ＋ᵣ (c ＋ᵣ d) = (a ＋ᵣ c) ＋ᵣ (b ＋ᵣ d)) ≔
begin
  assume a b c d;
  rewrite add_assoc a b (c ＋ᵣ d); rewrite left add_assoc b c d;
  rewrite add_com b c; rewrite add_assoc c b d;
  rewrite add_assoc a c (b ＋ᵣ d); reflexivity
end;

opaque symbol frac_eq N M D E : π (D ≠ zero) → π (E ≠ zero) →
  π (N *ᵣ E = M *ᵣ D) → π (N *ᵣ D ⁻¹ = M *ᵣ E ⁻¹) ≔
begin
  assume N M D E hD hE h;
  have l : π (N *ᵣ D ⁻¹ = ((N *ᵣ E) *ᵣ D ⁻¹) *ᵣ E ⁻¹)
  { rewrite mul_assoc N E (D ⁻¹); rewrite mul_com E (D ⁻¹);
    rewrite left mul_assoc N (D ⁻¹) E; rewrite mul_assoc (N *ᵣ D ⁻¹) E (E ⁻¹);
    rewrite mul_inv_r E hE; rewrite mul_one_r (N *ᵣ D ⁻¹); reflexivity };
  have r : π (M *ᵣ E ⁻¹ = ((M *ᵣ D) *ᵣ D ⁻¹) *ᵣ E ⁻¹)
  { rewrite mul_assoc M D (D ⁻¹); rewrite mul_inv_r D hD; rewrite mul_one_r M; reflexivity };
  rewrite l; rewrite r; rewrite h; reflexivity
end;

opaque symbol add_left_comm a b c : π (a ＋ᵣ (b ＋ᵣ c) = b ＋ᵣ (a ＋ᵣ c)) ≔
begin
  assume a b c;
  rewrite left add_assoc a b c; rewrite add_com a b; refine add_assoc b a c
end;

opaque symbol opp_add a b : π (—ᵣ (a ＋ᵣ b) = —ᵣ a ＋ᵣ —ᵣ b) ≔
begin
  assume a b; symmetry; refine eq_opp_of_add_zero (—ᵣ a ＋ᵣ —ᵣ b) (a ＋ᵣ b) _;
  rewrite add4 (—ᵣ a) (—ᵣ b) a b; rewrite add_opp_l a; rewrite add_opp_l b;
  refine add_zero_l zero
end;

opaque symbol opp_add_cancel_r a b : π (—ᵣ (a ＋ᵣ b) ＋ᵣ b = —ᵣ a) ≔
begin
  assume a b;
  rewrite opp_add a b; rewrite add_assoc (—ᵣ a) (—ᵣ b) b; rewrite add_opp_l b;
  refine add_zero_r (—ᵣ a)
end;

opaque symbol mul4 a b c d : π ((a *ᵣ b) *ᵣ (c *ᵣ d) = (a *ᵣ c) *ᵣ (b *ᵣ d)) ≔
begin
  assume a b c d;
  rewrite mul_assoc a b (c *ᵣ d); rewrite left mul_assoc b c d;
  rewrite mul_com b c; rewrite mul_assoc c b d;
  rewrite mul_assoc a c (b *ᵣ d); reflexivity
end;

opaque symbol inv_one : π (one ⁻¹ = one) ≔
begin
  rewrite left mul_one_l (one ⁻¹); refine mul_inv_r one one≠zero
end;

opaque symbol inv_mul_cancel_l c x : π (c ≠ zero) → π (c ⁻¹ *ᵣ (c *ᵣ x) = x) ≔
begin
  assume c x h;
  rewrite left mul_assoc (c ⁻¹) c x; rewrite mul_com (c ⁻¹) c; rewrite mul_inv_r c h;
  refine mul_one_l x
end;

opaque symbol mul_cancel_l c x y : π (c ≠ zero) → π (c *ᵣ x = c *ᵣ y) → π (x = y) ≔
begin
  assume c x y hc h;
  rewrite left inv_mul_cancel_l c x hc; rewrite left inv_mul_cancel_l c y hc;
  rewrite h; reflexivity
end;

// ===========================================================================
// D. Order lemmas
// ===========================================================================

// totality: derived from `sup_total` applied to the down-set {w | w ≤ y}.
opaque symbol le_total x y : π (x ≤ᵣ y ∨ y ≤ᵣ x) ≔
begin
  assume x y;
  have hs : π (has_sup (λ w, w ≤ᵣ y))
  { refine ∧ᵢ (∃ᵢ y (le_refl y)) (∃ᵢ y (λ w hw, hw)) };
  refine ∨ₑ (sup_total (λ w, w ≤ᵣ y) x hs) _ _
  { assume hd; refine ∃ₑ hd _; assume w hw;
    refine ∨ᵢ₁ (le_tr x w y (∧ₑ₂ hw) (∧ₑ₁ hw)) }
  { assume hle;
    refine ∨ᵢ₂ (le_tr y (sup (λ w, w ≤ᵣ y)) x
                  (sup_upper_bound (λ w, w ≤ᵣ y) hs y (le_refl y)) hle) }
end;

opaque symbol add_le_mono_r z x y : π (x ≤ᵣ y) → π (x ＋ᵣ z ≤ᵣ y ＋ᵣ z) ≔
begin
  assume z x y h; rewrite add_com x z; rewrite add_com y z; refine add_monotone z x y h
end;

opaque symbol add_le_mono a b c d : π (a ≤ᵣ b) → π (c ≤ᵣ d) → π (a ＋ᵣ c ≤ᵣ b ＋ᵣ d) ≔
begin
  assume a b c d hab hcd;
  refine le_tr (a ＋ᵣ c) (b ＋ᵣ c) (b ＋ᵣ d) (add_le_mono_r c a b hab) (add_monotone b c d hcd)
end;

opaque symbol add_le_cancel_l z x y : π (z ＋ᵣ x ≤ᵣ z ＋ᵣ y) → π (x ≤ᵣ y) ≔
begin
  assume z x y h;
  rewrite left add_opp_cancel_l z x; rewrite left add_opp_cancel_l z y;
  refine add_monotone (—ᵣ z) (z ＋ᵣ x) (z ＋ᵣ y) h
end;

// —ᵣ reverses ≤ᵣ
opaque symbol opp_le u v : π (u ≤ᵣ v) → π (—ᵣ v ≤ᵣ —ᵣ u) ≔
begin
  assume u v h;
  have l : π (u ＋ᵣ ((—ᵣ u) ＋ᵣ (—ᵣ v)) = —ᵣ v)
  { rewrite left add_assoc u (—ᵣ u) (—ᵣ v); rewrite add_opp_r u; refine add_zero_l (—ᵣ v) };
  have r : π (v ＋ᵣ ((—ᵣ u) ＋ᵣ (—ᵣ v)) = —ᵣ u)
  { rewrite add_com (—ᵣ u) (—ᵣ v); rewrite left add_assoc v (—ᵣ v) (—ᵣ u);
    rewrite add_opp_r v; refine add_zero_l (—ᵣ u) };
  rewrite left l; rewrite left .[X in _ ≤ᵣ X] r;
  refine add_le_mono_r ((—ᵣ u) ＋ᵣ (—ᵣ v)) u v h
end;

opaque symbol neg_of_nonpos x : π (x ≤ᵣ zero) → π (zero ≤ᵣ —ᵣ x) ≔
begin
  assume x h; rewrite left .[X in X ≤ᵣ _] opp_zero; refine opp_le x zero h
end;

opaque symbol opp_nonpos_of_nonneg x : π (zero ≤ᵣ x) → π (—ᵣ x ≤ᵣ zero) ≔
begin
  assume x h; rewrite left .[X in _ ≤ᵣ X] opp_zero; refine opp_le zero x h
end;

opaque symbol sub_nonneg_of_le a b : π (a ≤ᵣ b) → π (zero ≤ᵣ b −ᵣ a) ≔
begin
  assume a b h; rewrite left add_opp_r a; refine add_le_mono_r (—ᵣ a) a b h
end;

opaque symbol le_of_sub_nonneg a b : π (zero ≤ᵣ b −ᵣ a) → π (a ≤ᵣ b) ≔
begin
  assume a b h;
  rewrite left add_zero_l a; rewrite left sub_undo a b;
  refine add_le_mono_r a zero (b −ᵣ a) h
end;

opaque symbol le_of_sub_nonpos a b : π (b −ᵣ a ≤ᵣ zero) → π (b ≤ᵣ a) ≔
begin
  assume a b h;
  rewrite left sub_undo a b; rewrite left .[X in _ ≤ᵣ X] add_zero_l a;
  refine add_le_mono_r a (b −ᵣ a) zero h
end;

opaque symbol mul_le_mono_r c x y : π (zero ≤ᵣ c) → π (x ≤ᵣ y) → π (x *ᵣ c ≤ᵣ y *ᵣ c) ≔
begin
  assume c x y hc h; rewrite mul_com x c; rewrite mul_com y c; refine mul_monotone c x y hc h
end;

opaque symbol mul_nonneg a b : π (zero ≤ᵣ a) → π (zero ≤ᵣ b) → π (zero ≤ᵣ a *ᵣ b) ≔
begin
  assume a b ha hb; rewrite left mul_zero_r a; refine mul_monotone a zero b ha hb
end;

opaque symbol square_nonneg x : π (zero ≤ᵣ x *ᵣ x) ≔
begin
  assume x;
  refine ∨ₑ (le_total zero x) _ _
  // case 0 ≤ x
  { assume h; refine mul_nonneg x x h h }
  // case x ≤ 0
  { assume h; rewrite left mul_opp_opp x x;
    refine mul_nonneg (—ᵣ x) (—ᵣ x) (neg_of_nonpos x h) (neg_of_nonpos x h) }
end;

// monotonicity of squaring on the nonnegative reals
opaque symbol sqr_mono a b : π (zero ≤ᵣ a) → π (a ≤ᵣ b) → π (a *ᵣ a ≤ᵣ b *ᵣ b) ≔
begin
  assume a b h0 hab;
  refine le_tr (a *ᵣ a) (a *ᵣ b) (b *ᵣ b) (mul_monotone a a b h0 hab) _;
  refine mul_le_mono_r b a b (le_tr zero a b h0 hab) hab
end;

// constants

// 0 ≤ 1·1 = 1
opaque symbol zero_le_one : π (zero ≤ᵣ one) ≔
begin
  rewrite left mul_one_l one; refine square_nonneg one
end;

opaque symbol zero_le_two : π (zero ≤ᵣ two) ≔
begin
  rewrite left add_zero_l zero; refine add_le_mono zero one zero one zero_le_one zero_le_one
end;

opaque symbol one_le_two : π (one ≤ᵣ two) ≔
begin
  rewrite left .[X in X ≤ᵣ _] add_zero_r one; refine add_monotone one zero one zero_le_one
end;

opaque symbol not_one_le_zero : π (one ≤ᵣ zero) → π ⊥ ≔
begin
  assume h; refine one≠zero (le_antisymmetric one zero h zero_le_one)
end;

opaque symbol not_two_le_zero : π (two ≤ᵣ zero) → π ⊥ ≔
begin
  assume h; refine not_one_le_zero (le_tr one two zero one_le_two h)
end;

opaque symbol not_two_le_one : π (two ≤ᵣ one) → π ⊥ ≔
begin
  assume h; refine one≠zero (add_cancel_l one one zero _);
  rewrite add_zero_r one; refine le_antisymmetric two one h one_le_two
end;

// ===========================================================================
// F. Embedding of the rationals (alethe.rat) into the reals
//
//   of_pos  : ℙ → real        by the binary structure (O p ↦ p + p, I p ↦ p + p + 1)
//   of_int  : ℤ → real        multiplicative (of_int_mul)
//   of_frac : ℤ × ℙ → real    n ‚ d ↦ of_int n · (of_pos d)⁻¹
//   of_rat  : ℚ → real        of_frac lifted through the quotient: fractions
//                             related by ≅ have the same image
//                             (of_frac_compat)
//
// `of_rat` is registered as the coercion from ℚ to real.
// ===========================================================================

// ℙ → real
symbol of_pos : ℙ → τ real;
rule of_pos H ↪ one
with of_pos (O $p) ↪ of_pos $p ＋ᵣ of_pos $p
with of_pos (I $p) ↪ (of_pos $p ＋ᵣ of_pos $p) ＋ᵣ one;

opaque symbol of_pos_succ p : π (of_pos (succ p) = of_pos p ＋ᵣ one) ≔
begin
  induction
  // case I
  { assume p prec; simplify; rewrite prec;
    rewrite add4 (of_pos p) one (of_pos p) one;
    rewrite add_assoc (of_pos p ＋ᵣ of_pos p) one one; reflexivity }
  // case O
  { assume p prec; reflexivity }
  // case H
  { reflexivity }
end;

opaque symbol of_pos_add p q : π (of_pos (add p q) = of_pos p ＋ᵣ of_pos q) ≔
begin
  assume p q;
  refine ind_ℙeano (λ p, of_pos (add p q) = of_pos p ＋ᵣ of_pos q) _ _ p
  // case H
  { change π (of_pos (add H q) = one ＋ᵣ of_pos q);
    rewrite addHn q; rewrite of_pos_succ q; refine add_com (of_pos q) one }
  // case succ
  { assume x xrec;
    rewrite add_succ x q; rewrite of_pos_succ (add x q); rewrite of_pos_succ x; rewrite xrec;
    rewrite add_assoc (of_pos x) (of_pos q) one; rewrite add_com (of_pos q) one;
    rewrite add_assoc (of_pos x) one (of_pos q); reflexivity }
end;

opaque symbol of_pos_mul p q : π (of_pos (mul p q) = of_pos p *ᵣ of_pos q) ≔
begin
  assume p q;
  refine ind_ℙeano (λ p, of_pos (mul p q) = of_pos p *ᵣ of_pos q) _ _ p
  // case H
  { simplify; symmetry; refine mul_one_l (of_pos q) }
  // case succ
  { assume x xrec;
    rewrite mul_succ x q; rewrite of_pos_add (mul x q) q; rewrite xrec;
    rewrite of_pos_succ x; rewrite mul_distr_r (of_pos x) one (of_pos q);
    rewrite mul_one_l (of_pos q); reflexivity }
end;

opaque symbol one_le_of_pos p : π (one ≤ᵣ of_pos p) ≔
begin
  assume p;
  refine ind_ℙeano (λ p, one ≤ᵣ of_pos p) (le_refl one) _ p;
  assume x xrec; rewrite of_pos_succ x; rewrite left .[X in X ≤ᵣ _] add_zero_l one;
  refine add_le_mono_r one zero (of_pos x) (le_tr zero one (of_pos x) zero_le_one xrec)
end;

opaque symbol of_pos≠zero p : π (of_pos p ≠ zero) ≔
begin
  assume p h; refine not_one_le_zero _; rewrite left h; refine one_le_of_pos p
end;

symbol of_int : ℤ → τ real;
rule of_int Z0 ↪ zero
with of_int (Zpos $p) ↪ of_pos $p
with of_int (Zneg $p) ↪ —ᵣ (of_pos $p);

opaque symbol of_int_mul a b : π (of_int (a * b) = of_int a *ᵣ of_int b) ≔
begin
  induction
  // case Z0
  { assume b; symmetry; refine mul_zero_l (of_int b) }
  // case Zpos
  { assume p;
    induction
    { symmetry; refine mul_zero_r (of_pos p) }
    { assume q; refine of_pos_mul p q }
    { assume q; simplify; rewrite of_pos_mul p q; symmetry; refine mul_neg_r (of_pos p) (of_pos q) } }
  // case Zneg
  { assume p;
    induction
    { symmetry; refine mul_zero_r (—ᵣ (of_pos p)) }
    { assume q; simplify; rewrite of_pos_mul p q; symmetry; refine neg_mul (of_pos p) (of_pos q) }
    { assume q; simplify; rewrite of_pos_mul p q; symmetry; refine mul_opp_opp (of_pos p) (of_pos q) } }
end;

symbol of_frac (x : τ (int × pos)) : τ real ≔ of_int (x ₁) *ᵣ (of_pos (x ₂)) ⁻¹;

opaque symbol of_frac_compat x y : π (x ≅ y) → π (of_frac x = of_frac y) ≔
begin
  induction; assume n d;
  induction; assume m e h;
  simplify;
  refine frac_eq (of_int n) (of_int m) (of_pos d) (of_pos e) (of_pos≠zero d) (of_pos≠zero e) _;
  have h' : π (of_int (n * Zpos e) = of_int (m * Zpos d))
  { refine feq of_int h };
  have hn : π (of_int (n * Zpos e) = of_int n *ᵣ of_pos e)
  { refine of_int_mul n (Zpos e) };
  have hm : π (of_int (m * Zpos d) = of_int m *ᵣ of_pos d)
  { refine of_int_mul m (Zpos d) };
  rewrite left hn; rewrite left hm; refine h'
end;

// of_int is additive: by induction on a positive summand, then by negation.
opaque symbol of_int_opp z : π (of_int (— z) = —ᵣ of_int z) ≔
begin
  induction
  { symmetry; refine opp_zero }
  { assume p; reflexivity }
  { assume p; symmetry; refine opp_opp (of_pos p) }
end;

opaque symbol of_pos_ppd p : π (of_pos (pos_pred_double p) ＋ᵣ one = of_pos p ＋ᵣ of_pos p) ≔
begin
  assume p; rewrite left of_pos_succ (pos_pred_double p); rewrite succ_pos_pred_double p;
  reflexivity
end;

opaque symbol of_int_succ x : π (of_int (x + Zpos H) = of_int x ＋ᵣ one) ≔
begin
  induction
  // case Z0
  { symmetry; refine add_zero_l one }
  // case Zpos
  { assume p; refine of_pos_add p H }
  // case Zneg: Zneg p + 1 is sub H p
  { induction
    { assume q h;
      change π (—ᵣ (of_pos q ＋ᵣ of_pos q) = —ᵣ ((of_pos q ＋ᵣ of_pos q) ＋ᵣ one) ＋ᵣ one);
      symmetry; refine opp_add_cancel_r (of_pos q ＋ᵣ of_pos q) one }
    { assume q h;
      change π (—ᵣ of_pos (pos_pred_double q) = —ᵣ (of_pos q ＋ᵣ of_pos q) ＋ᵣ one);
      rewrite left of_pos_ppd q; symmetry; refine opp_add_cancel_r (of_pos (pos_pred_double q)) one }
    { symmetry; refine add_opp_l one } }
end;

opaque symbol of_int_add_pos x q : π (of_int (x + Zpos q) = of_int x ＋ᵣ of_pos q) ≔
begin
  assume x q;
  refine ind_ℙeano (λ q, of_int (x + Zpos q) = of_int x ＋ᵣ of_pos q) (of_int_succ x) _ q;
  assume r h;
  rewrite add_Zpos_succ x r; rewrite of_int_succ (x + Zpos r); rewrite h;
  rewrite of_pos_succ r; refine add_assoc (of_int x) (of_pos r) one
end;

opaque symbol of_int_add x y : π (of_int (x + y) = of_int x ＋ᵣ of_int y) ≔
begin
  assume x;
  induction
  { rewrite +Z0 x; symmetry; refine add_zero_r (of_int x) }
  { assume q; refine of_int_add_pos x q }
  { assume q;
    have e : π (x + Zneg q = — (— x + Zpos q))
    { rewrite distr_—_+ (— x) (Zpos q); rewrite —_idem x; reflexivity };
    rewrite e; rewrite of_int_opp (— x + Zpos q); rewrite of_int_add_pos (— x) q;
    rewrite of_int_opp x; rewrite opp_add (—ᵣ of_int x) (of_pos q); rewrite opp_opp (of_int x);
    reflexivity }
end;

symbol of_rat : ℚ → τ real ≔ lift (≅) of_frac of_frac_compat;

assert (n : ℤ) (d : ℙ) ⊢ of_rat (n / d) ≡ of_int n *ᵣ (of_pos d) ⁻¹;
assert ⊢ of_rat 1⫽1 ≡ one *ᵣ one ⁻¹;

// of_rat is a ring morphism. Each equation is shown after multiplying both
// sides by the (nonzero) common denominator.
opaque symbol of_frac_den n d : π (of_pos d *ᵣ of_frac (n ‚ d) = of_int n) ≔
begin
  assume n d; refine mul_inv_cancel (of_pos d) (of_int n) (of_pos≠zero d)
end;

opaque symbol of_rat_add (x y : τ rat) : π (of_rat (x 𝕢+ y) = of_rat x ＋ᵣ of_rat y) ≔
begin
  induction; induction; assume a p; induction; induction; assume b q;
  change π (of_frac ((a * Zpos q + b * Zpos p) ‚ mul p q) = of_frac (a ‚ p) ＋ᵣ of_frac (b ‚ q));
  refine mul_cancel_l (of_pos (mul p q)) _ _ (of_pos≠zero (mul p q)) _;
  rewrite of_frac_den (a * Zpos q + b * Zpos p) (mul p q);
  rewrite of_int_add (a * Zpos q) (b * Zpos p);
  rewrite of_int_mul a (Zpos q); rewrite of_int_mul b (Zpos p);
  rewrite of_pos_mul p q;
  rewrite mul_distr_l (of_pos p *ᵣ of_pos q) (of_frac (a ‚ p)) (of_frac (b ‚ q));
  rewrite mul_assoc (of_pos p) (of_pos q) (of_frac (b ‚ q));
  rewrite of_frac_den b q;
  rewrite mul_com (of_pos p) (of_pos q);
  rewrite mul_assoc (of_pos q) (of_pos p) (of_frac (a ‚ p));
  rewrite of_frac_den a p;
  rewrite mul_com (of_pos q) (of_int a); rewrite mul_com (of_pos p) (of_int b);
  reflexivity
end;

opaque symbol of_rat_mul (x y : τ rat) : π (of_rat (x *𝕢 y) = of_rat x *ᵣ of_rat y) ≔
begin
  induction; induction; assume a p; induction; induction; assume b q;
  change π (of_frac ((a * b) ‚ mul p q) = of_frac (a ‚ p) *ᵣ of_frac (b ‚ q));
  refine mul_cancel_l (of_pos (mul p q)) _ _ (of_pos≠zero (mul p q)) _;
  rewrite of_frac_den (a * b) (mul p q); rewrite of_int_mul a b;
  rewrite of_pos_mul p q;
  rewrite mul4 (of_pos p) (of_pos q) (of_frac (a ‚ p)) (of_frac (b ‚ q));
  rewrite of_frac_den a p; rewrite of_frac_den b q; reflexivity
end;

opaque symbol of_rat_one : π (of_rat 1⫽1 = one) ≔
begin
  refine mul_inv_r one one≠zero
end;

// ===========================================================================
// G. Real literals
//
// of_rat computes (of_rat (2 / H) reduces to (one ＋ᵣ one) *ᵣ one ⁻¹), so no
// rewrite rule can recognise a rational inside a real term. A literal is
// written `lit q` instead: a constant, defined by its one axiom `lit_def`.
// Defining a fresh constant this way cannot make the theory inconsistent.
// ===========================================================================

constant symbol lit : ℚ → τ real;

symbol lit_def q : π (lit q = of_rat q);

// a rational can be used where a real is expected
coerce_rule coerce (Quot (≅)) (τ real) $x ↪ lit $x;

opaque symbol lit_add (x y : τ rat) : π (lit (x 𝕢+ y) = lit x ＋ᵣ lit y) ≔
begin
  assume x y; rewrite lit_def (x 𝕢+ y); rewrite lit_def x; rewrite lit_def y;
  refine of_rat_add x y
end;

opaque symbol lit_mul (x y : τ rat) : π (lit (x *𝕢 y) = lit x *ᵣ lit y) ≔
begin
  assume x y; rewrite lit_def (x *𝕢 y); rewrite lit_def x; rewrite lit_def y;
  refine of_rat_mul x y
end;

opaque symbol lit_one : π (lit 1⫽1 = one) ≔
begin
  rewrite lit_def 1⫽1; refine of_rat_one
end;

opaque symbol lit_opp_one : π (lit (—𝕢 1⫽1) = —ᵣ one) ≔
begin
  rewrite lit_def (—𝕢 1⫽1);
  change π ((—ᵣ one) *ᵣ one ⁻¹ = —ᵣ one); rewrite inv_one; refine mul_one_r (—ᵣ one)
end;

opaque symbol lit_zero d : π (lit (cl (0 ‚ d)) = zero) ≔
begin
  assume d; rewrite lit_def (cl (0 ‚ d)); refine mul_zero_l ((of_pos d) ⁻¹)
end;

assert (x : ℚ) (a : τ real) ⊢ a *ᵣ x ≡ a *ᵣ lit x;
