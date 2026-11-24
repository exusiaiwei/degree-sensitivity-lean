module

public import DegreeSensitivity.Symmetrisation
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
# Sharp Degree-4 Sensitivity Upper Bound: `deg(f) ≤ 4 → s(f) ≤ 9`

We formalize a completely elementary, zero-branching algebraic proof of the
impossibility of `(n = 10, d = 4)` (i.e., `deg(f) ≤ 4 → maxSensitivity f ≤ 9`
for every Boolean function `f` on any number of variables), matching the
composed witness `NAE₃ ∘ NAE₃` (`n = 9, d = 4, s = 9`).

## Proof outline
Suppose `f : BooleanFun 10` has `polyDegree f ≤ 4`, `f 0 = false`, and
`f (e_i) = true` for all `i : Fin 10`.
1. (`deg4_dim10_step1`) Symmetrisation on `f` (deg ≤ 4) forces `p(2) = 1, p(5) = 0,
   p(8) = 1, p(10) = 0` (so `f` is constant on layers `1, 2, 5, 8`) and `S_3 = 70`.
2. (`deg4_dim10_step2`) For distinct `a, b : Fin 10`, the 8-variable coordinate difference
   `h₁(z) = f(1_a, 0_b, z) - f(0_a, 1_b, z)` has multilinear degree `≤ 3` and
   vanishes on layers `0, 1, 4, 7`. Symmetrisation forces `H₁(2) = 0`, so every
   coordinate has the same layer-3 degree `D(a) = D(b)`.
3. (`deg4_dim10_step3`) For 4 distinct `a, b, c, d : Fin 10`, the 6-variable second
   difference `h₂(y)` has multilinear degree `≤ 2` and vanishes on layers `0, 3, 6`.
   Symmetrisation forces `H₂(1) = 0`, yielding `d(a,c) + d(b,d) = d(a,d) + d(b,c)`.
4. (`no_normalized_deg4_dim10`) Summing over the 7 choices of `d ∉ {a,b,c}` shows
   `d(a, b) = K` is constant across all `90` ordered distinct pairs `(a, b)`.
   Double-counting layer-3 triples gives `90 * K = 6 * S_3 = 420`, impossible in `ℕ`.
-/

namespace DegreeSensitivity

open scoped BigOperators

/-! ### Helper lemmas for constant layers and powerset splitting -/

private lemma eq_true_of_layerAvg_eq_one {m k : ℕ} {f : BooleanFun m} (hk : k ≤ m)
    (havg : layerAvg (fun x => boolToReal (f x)) k = 1)
    {x : Fin m → Bool} (hx : x ∈ hammingLayer m k) : f x = true := by
  rw [layerAvg, realLayerSum_bool] at havg
  have hpos : (Nat.choose m k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have hS : (boolLayerSum f k : ℝ) = (Nat.choose m k : ℝ) := by
    rwa [div_eq_one_iff_eq hpos] at havg
  have hSNat : boolLayerSum f k = (hammingLayer m k).card := by
    rw [card_hammingLayer]
    exact_mod_cast hS
  have hfilt : (hammingLayer m k).filter (fun y => f y = true) = hammingLayer m k :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (le_of_eq hSNat.symm)
  have hmem : x ∈ (hammingLayer m k).filter (fun y => f y = true) := by rwa [hfilt]
  exact (Finset.mem_filter.mp hmem).2

private lemma eq_false_of_layerAvg_eq_zero {m k : ℕ} {f : BooleanFun m} (hk : k ≤ m)
    (havg : layerAvg (fun x => boolToReal (f x)) k = 0)
    {x : Fin m → Bool} (hx : x ∈ hammingLayer m k) : f x = false := by
  rw [layerAvg, realLayerSum_bool] at havg
  have hpos : (Nat.choose m k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have hS : (boolLayerSum f k : ℝ) = 0 := by
    rcases div_eq_zero_iff.mp havg with h0 | h0
    · exact h0
    · exact absurd h0 hpos
  have hSNat : boolLayerSum f k = 0 := by exact_mod_cast hS
  have hemp : (hammingLayer m k).filter (fun y => f y = true) = ∅ :=
    Finset.card_eq_zero.mp hSNat
  cases hfx : f x
  · rfl
  · exfalso
    have hmem : x ∈ (hammingLayer m k).filter (fun y => f y = true) :=
      Finset.mem_filter.mpr ⟨hx, hfx⟩
    rw [hemp] at hmem
    exact Finset.notMem_empty x hmem

private lemma sum_powerset_insert {α : Type*} [DecidableEq α] (c : Finset α → ℝ)
    {a : α} {A : Finset α} (ha : a ∉ A) :
    ∑ S ∈ (insert a A).powerset, c S =
      ∑ T ∈ A.powerset, c T + ∑ T ∈ A.powerset, c (insert a T) := by
  rw [Finset.powerset_insert]
  have hdisj : Disjoint A.powerset (A.powerset.image (insert a)) := by
    rw [Finset.disjoint_left]
    intro S hS1 hS2
    rw [Finset.mem_image] at hS2
    obtain ⟨T, _, rfl⟩ := hS2
    exact ha (Finset.mem_powerset.mp hS1 (Finset.mem_insert_self a T))
  rw [Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image]
  intro T₁ hT₁ T₂ hT₂ hEq
  have ha1 : a ∉ T₁ := fun h => ha (Finset.mem_powerset.mp hT₁ h)
  have ha2 : a ∉ T₂ := fun h => ha (Finset.mem_powerset.mp hT₂ h)
  have := congrArg (fun S => S.erase a) hEq
  simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this

private lemma sum_mobius_powerset {m : ℕ} (f : BooleanFun m) (A : Finset (Fin m)) :
    ∑ S ∈ A.powerset, (mobiusCoeff f S : ℝ) = boolToReal (f (indicator A)) := by
  have h := representsPoly_mobius f (indicator A)
  change MvPolynomial.eval (fun i => boolToReal (indicator A i))
    (multilinearPoly (fun S => (mobiusCoeff f S : ℝ))) = boolToReal (f (indicator A)) at h
  rw [eval_multilinearPoly, supportOf_indicator] at h
  exact h

private lemma sum_powerset_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    (φ : α → β) (hφ : Function.Injective φ) (A : Finset α) (F : Finset β → ℝ) :
    ∑ S ∈ (A.image φ).powerset, F S = ∑ T ∈ A.powerset, F (T.image φ) := by
  classical
  rw [← Finset.sum_image (g := fun T : Finset α => T.image φ)]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext S
    simp only [Finset.mem_powerset, Finset.mem_image]
    constructor
    · intro hS
      refine ⟨A.filter (fun x => φ x ∈ S), Finset.filter_subset _ _, ?_⟩
      ext y
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨_, hφx⟩, rfl⟩; exact hφx
      · intro hy
        obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.mp (hS hy)
        exact ⟨x, ⟨hxA, hy⟩, rfl⟩
    · rintro ⟨T, hTA, rfl⟩
      exact Finset.image_subset_image hTA
  · intro T₁ _ T₂ _ hEq
    exact Finset.image_injective hφ hEq

/-! ### Layer-3 degrees and codegrees on `Fin 10` -/

private def layer3Deg (f : BooleanFun 10) (a : Fin 10) : ℕ :=
  ((hammingLayer 10 3).filter (fun x => f x = true ∧ x a = true)).card

private def layer3Codeg (f : BooleanFun 10) (a b : Fin 10) : ℕ :=
  ((hammingLayer 10 3).filter (fun x => f x = true ∧ x a = true ∧ x b = true)).card

private lemma layer3Codeg_comm (f : BooleanFun 10) (a b : Fin 10) :
    layer3Codeg f a b = layer3Codeg f b a := by
  unfold layer3Codeg
  congr 1
  ext x
  simp [and_comm]

private lemma sum_layer3Deg (f : BooleanFun 10) :
    ∑ a : Fin 10, layer3Deg f a = 3 * boolLayerSum f 3 := by
  classical
  have h1 : ∑ a : Fin 10, layer3Deg f a =
      ∑ a : Fin 10, ∑ x ∈ (hammingLayer 10 3).filter (fun x => f x = true),
        if x a = true then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [layer3Deg, Finset.sum_boole, Nat.cast_id]
    congr 1
    ext x
    simp [Finset.mem_filter, and_assoc]
  rw [h1, Finset.sum_comm]
  calc ∑ x ∈ (hammingLayer 10 3).filter (fun x => f x = true),
        ∑ a : Fin 10, (if x a = true then 1 else 0)
      = ∑ x ∈ (hammingLayer 10 3).filter (fun x => f x = true), 3 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxL : x ∈ hammingLayer 10 3 := (Finset.mem_filter.mp hx).1
        have hcard : (supportOf x).card = 3 := (Finset.mem_filter.mp hxL).2
        rw [Finset.sum_boole, Nat.cast_id]
        exact hcard
    _ = 3 * boolLayerSum f 3 := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm, boolLayerSum]

private lemma sum_layer3Codeg_erase (f : BooleanFun 10) (a : Fin 10) :
    ∑ b ∈ Finset.univ.erase a, layer3Codeg f a b = 2 * layer3Deg f a := by
  classical
  have h1 : ∑ b ∈ Finset.univ.erase a, layer3Codeg f a b =
      ∑ b ∈ Finset.univ.erase a,
        ∑ x ∈ (hammingLayer 10 3).filter (fun x => f x = true ∧ x a = true),
          if x b = true then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro b _
    rw [layer3Codeg, Finset.sum_boole, Nat.cast_id]
    congr 1
    ext x
    simp [Finset.mem_filter, and_assoc]
  rw [h1, Finset.sum_comm]
  calc ∑ x ∈ (hammingLayer 10 3).filter (fun x => f x = true ∧ x a = true),
        ∑ b ∈ Finset.univ.erase a, (if x b = true then 1 else 0)
      = ∑ x ∈ (hammingLayer 10 3).filter (fun x => f x = true ∧ x a = true), 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        obtain ⟨hxL, _, hxa⟩ := Finset.mem_filter.mp hx
        have hcard : (supportOf x).card = 3 := (Finset.mem_filter.mp hxL).2
        have haMem : a ∈ supportOf x := mem_supportOf.mpr hxa
        rw [Finset.sum_boole, Nat.cast_id]
        have heq : (Finset.univ.erase a).filter (fun b => x b = true) = (supportOf x).erase a := by
          ext b
          simp [supportOf, and_comm]
        rw [heq, Finset.card_erase_of_mem haMem, hcard]
    _ = 2 * layer3Deg f a := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm, layer3Deg]

/-! ### Step 1: Constant layers `{1, 2, 5, 8}` and `S_3 = 70` -/

private lemma deg4_dim10_step1 {f : BooleanFun 10} (hf : polyDegree f ≤ 4)
    (hf0 : f (zeroVec 10) = false) (hf1 : ∀ i : Fin 10, f (basisVec i) = true) :
    (∀ x ∈ hammingLayer 10 1, f x = true) ∧
    (∀ x ∈ hammingLayer 10 2, f x = true) ∧
    (∀ x ∈ hammingLayer 10 5, f x = false) ∧
    (∀ x ∈ hammingLayer 10 8, f x = true) ∧
    boolLayerSum f 3 = 70 := by
  let p : ℕ → ℝ := fun k => layerAvg (fun x => boolToReal (f x)) k
  have hp0 : p 0 = 0 := layerAvg_bool_zero hf0
  have hp1 : p 1 = 1 := layerAvg_bool_one (by decide) hf1
  have hp2_le : p 2 ≤ 1 := layerAvg_bool_le_one f 2 (by decide)
  have hp5_ge : 0 ≤ p 5 := layerAvg_bool_nonneg f 5
  have hp8_le : p 8 ≤ 1 := layerAvg_bool_le_one f 8 (by decide)
  have hp10_ge : 0 ≤ p 10 := layerAvg_bool_nonneg f 10

  have hid1 := bool_symmetrisation_linear_identity f hf
    ![-63, 200, -175, 0, 0, 56, 0, 0, -25, 0, 7] (by decide)
  change ∑ k : Fin 11, ((![(-63 : ℤ), 200, -175, 0, 0, 56, 0, 0, -25, 0, 7] k : ℤ) : ℝ) * p k.1 = 0
    at hid1
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one] at hid1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ,
    Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_mul, zero_add] at hid1
  have hp2 : p 2 = 1 := by linarith
  have hp5 : p 5 = 0 := by linarith
  have hp8 : p 8 = 1 := by linarith

  have hid2 := bool_symmetrisation_linear_identity f hf
    ![21, -90, 140, -84, 0, 14, 0, 0, -1, 0, 0] (by decide)
  change ∑ k : Fin 11, ((![(21 : ℤ), -90, 140, -84, 0, 14, 0, 0, -1, 0, 0] k : ℤ) : ℝ) * p k.1 = 0
    at hid2
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one] at hid2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ,
    Int.cast_neg, Int.cast_ofNat, Int.cast_zero, Int.cast_one, zero_mul, add_zero, zero_add] at hid2
  have hp3 : p 3 = 7 / 12 := by linarith
  have hS3 : boolLayerSum f 3 = 70 := by
    have havg : (boolLayerSum f 3 : ℝ) / (Nat.choose 10 3 : ℝ) = 7 / 12 := by
      simpa [p, layerAvg, realLayerSum_bool] using hp3
    have hch : (Nat.choose 10 3 : ℝ) = 120 := by
      exact_mod_cast (by decide : Nat.choose 10 3 = 120)
    rw [hch] at havg
    have hR : (boolLayerSum f 3 : ℝ) = 70 := by linarith
    exact_mod_cast hR

  refine ⟨fun x hx => eq_true_of_layerAvg_eq_one (by decide) hp1 hx,
          fun x hx => eq_true_of_layerAvg_eq_one (by decide) hp2 hx,
          fun x hx => eq_false_of_layerAvg_eq_zero (by decide) hp5 hx,
          fun x hx => eq_true_of_layerAvg_eq_one (by decide) hp8 hx,
          hS3⟩

/-! ### Step 2: Equal layer-3 degrees `layer3Deg f a = layer3Deg f b` -/

private lemma deg4_dim10_step2 {f : BooleanFun 10} (hf : polyDegree f ≤ 4)
    (hf_l1 : ∀ x ∈ hammingLayer 10 1, f x = true)
    (hf_l2 : ∀ x ∈ hammingLayer 10 2, f x = true)
    (hf_l5 : ∀ x ∈ hammingLayer 10 5, f x = false)
    (hf_l8 : ∀ x ∈ hammingLayer 10 8, f x = true)
    (a b : Fin 10) : layer3Deg f a = layer3Deg f b := by
  classical
  by_cases hab : a = b
  · subst hab; rfl
  let R : Finset (Fin 10) := (Finset.univ.erase a).erase b
  have hRcard : R.card = 8 := by
    have hbMem : b ∈ (Finset.univ : Finset (Fin 10)).erase a :=
      Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
    rw [Finset.card_erase_of_mem hbMem, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin]
  let eR : Fin 8 ≃ R := (Fintype.equivFinOfCardEq (by simp [hRcard])).symm
  let φ : Fin 8 → Fin 10 := fun i => (eR i).1
  have hφ_inj : Function.Injective φ := fun i₁ i₂ h => eR.injective (Subtype.ext h)
  have hφ_ne_a : ∀ i, φ i ≠ a := fun i =>
    (Finset.mem_erase.mp (Finset.mem_erase.mp (eR i).2).2).1
  have hφ_ne_b : ∀ i, φ i ≠ b := fun i => (Finset.mem_erase.mp (eR i).2).1
  have hφ_surj : ∀ u ∈ R, ∃ i : Fin 8, φ i = u := fun u hu =>
    ⟨eR.symm ⟨u, hu⟩, by simp [φ]⟩
  let liftA : (Fin 8 → Bool) → (Fin 10 → Bool) := fun z =>
    indicator (insert a ((supportOf z).image φ))
  let liftB : (Fin 8 → Bool) → (Fin 10 → Bool) := fun z =>
    indicator (insert b ((supportOf z).image φ))
  let h1 : (Fin 8 → Bool) → ℝ := fun z =>
    boolToReal (f (liftA z)) - boolToReal (f (liftB z))
  let c1 : Finset (Fin 8) → ℝ := fun T =>
    (mobiusCoeff f (insert a (T.image φ)) : ℝ) - (mobiusCoeff f (insert b (T.image φ)) : ℝ)
  have h1_rep : ∀ z : Fin 8 → Bool, ∑ T ∈ (supportOf z).powerset, c1 T = h1 z := by
    intro z
    have haNot : a ∉ (supportOf z).image φ := by
      simp only [Finset.mem_image, not_exists, not_and]; intro i _; exact hφ_ne_a i
    have hbNot : b ∉ (supportOf z).image φ := by
      simp only [Finset.mem_image, not_exists, not_and]; intro i _; exact hφ_ne_b i
    have hA := sum_mobius_powerset f (insert a ((supportOf z).image φ))
    have hB := sum_mobius_powerset f (insert b ((supportOf z).image φ))
    rw [sum_powerset_insert _ haNot] at hA
    rw [sum_powerset_insert _ hbNot] at hB
    have hsub : boolToReal (f (liftA z)) - boolToReal (f (liftB z)) =
        ∑ T ∈ ((supportOf z).image φ).powerset,
          ((mobiusCoeff f (insert a T) : ℝ) - (mobiusCoeff f (insert b T) : ℝ)) := by
      rw [Finset.sum_sub_distrib]
      linarith
    rw [show h1 z = boolToReal (f (liftA z)) - boolToReal (f (liftB z)) from rfl, hsub]
    exact (sum_powerset_image φ hφ_inj (supportOf z)
      (fun T => (mobiusCoeff f (insert a T) : ℝ) - (mobiusCoeff f (insert b T) : ℝ))).symm
  have h1_deg : ∀ T : Finset (Fin 8), 3 < T.card → c1 T = 0 := by
    intro T hT
    have haNot : a ∉ T.image φ := by
      simp only [Finset.mem_image, not_exists, not_and]; intro i _; exact hφ_ne_a i
    have hbNot : b ∉ T.image φ := by
      simp only [Finset.mem_image, not_exists, not_and]; intro i _; exact hφ_ne_b i
    have hca : polyDegree f < (insert a (T.image φ)).card := by
      rw [Finset.card_insert_of_notMem haNot, Finset.card_image_of_injective T hφ_inj]; omega
    have hcb : polyDegree f < (insert b (T.image φ)).card := by
      rw [Finset.card_insert_of_notMem hbNot, Finset.card_image_of_injective T hφ_inj]; omega
    simp [c1, mobiusCoeff_eq_zero_of_polyDegree_lt hca, mobiusCoeff_eq_zero_of_polyDegree_lt hcb]
  have h1_lift_mem : ∀ (r : ℕ) (z : Fin 8 → Bool), z ∈ hammingLayer 8 r →
      liftA z ∈ hammingLayer 10 (r + 1) ∧ liftB z ∈ hammingLayer 10 (r + 1) := by
    intro r z hz
    have hrc : (supportOf z).card = r := (Finset.mem_filter.mp hz).2
    have haNot : a ∉ (supportOf z).image φ := by
      simp only [Finset.mem_image, not_exists, not_and]; intro i _; exact hφ_ne_a i
    have hbNot : b ∉ (supportOf z).image φ := by
      simp only [Finset.mem_image, not_exists, not_and]; intro i _; exact hφ_ne_b i
    constructor
    · rw [hammingLayer, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by
        simp [liftA, Finset.card_insert_of_notMem haNot, Finset.card_image_of_injective _ hφ_inj, hrc]⟩
    · rw [hammingLayer, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by
        simp [liftB, Finset.card_insert_of_notMem hbNot, Finset.card_image_of_injective _ hφ_inj, hrc]⟩
  have h1_zero_layer : ∀ r : ℕ, (∀ x ∈ hammingLayer 10 (r + 1), f x = true) ∨
      (∀ x ∈ hammingLayer 10 (r + 1), f x = false) → layerAvg h1 r = 0 := by
    intro r hconst
    rw [layerAvg, realLayerSum]
    have hsum0 : ∑ z ∈ hammingLayer 8 r, h1 z = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      obtain ⟨hA, hB⟩ := h1_lift_mem r z hz
      rcases hconst with ht | hff
      · simp [h1, ht _ hA, ht _ hB]
      · simp [h1, hff _ hA, hff _ hB]
    rw [hsum0, zero_div]
  have hH0 : layerAvg h1 0 = 0 := h1_zero_layer 0 (Or.inl hf_l1)
  have hH1 : layerAvg h1 1 = 0 := h1_zero_layer 1 (Or.inl hf_l2)
  have hH4 : layerAvg h1 4 = 0 := h1_zero_layer 4 (Or.inr hf_l5)
  have hH7 : layerAvg h1 7 = 0 := h1_zero_layer 7 (Or.inl hf_l8)
  have hid_h1 := symmetrisation_linear_identity h1 c1 h1_rep h1_deg
    ![-45, 140, -126, 0, 35, 0, 0, -4, 0] (by decide)
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_one] at hid_h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ,
    Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_mul, add_zero, zero_add] at hid_h1
  have hH2 : layerAvg h1 2 = 0 := by linarith
  have hsum2 : realLayerSum h1 2 = 0 := by
    rw [layerAvg] at hH2
    have hch : (Nat.choose 8 2 : ℝ) ≠ 0 := by exact_mod_cast (by decide : Nat.choose 8 2 ≠ 0)
    exact (div_eq_zero_iff.mp hH2).resolve_right hch
  have hcardA : ∑ z ∈ hammingLayer 8 2, boolToReal (f (liftA z)) =
      (((hammingLayer 10 3).filter (fun x => f x = true ∧ x a = true ∧ x b = false)).card : ℝ) := by
    simp only [boolToReal]
    rw [Finset.sum_boole]
    apply congrArg (Nat.cast : ℕ → ℝ)
    apply Finset.card_bij (fun z _ => liftA z)
    · intro z hz
      obtain ⟨hzL, hfz⟩ := Finset.mem_filter.mp hz
      rw [Finset.mem_filter]
      refine ⟨(h1_lift_mem 2 z hzL).1, hfz, ?_, ?_⟩
      · simp [liftA, indicator]
      · have hbNot : b ∉ insert a ((supportOf z).image φ) := by
          simp only [Finset.mem_insert, Finset.mem_image, not_or, not_exists, not_and]
          exact ⟨Ne.symm hab, fun i _ => hφ_ne_b i⟩
        simp [liftA, indicator, hbNot]
    · intro z₁ _ z₂ _ hEq
      have hsupp : insert a ((supportOf z₁).image φ) = insert a ((supportOf z₂).image φ) := by
        have := congrArg supportOf hEq
        simpa [liftA] using this
      have ha1 : a ∉ (supportOf z₁).image φ := by
        simp only [Finset.mem_image, not_exists, not_and]; intro i _; exact hφ_ne_a i
      have ha2 : a ∉ (supportOf z₂).image φ := by
        simp only [Finset.mem_image, not_exists, not_and]; intro i _; exact hφ_ne_a i
      have himg : (supportOf z₁).image φ = (supportOf z₂).image φ := by
        have := congrArg (fun S => S.erase a) hsupp
        simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this
      have hsz : supportOf z₁ = supportOf z₂ := Finset.image_injective hφ_inj himg
      have := congrArg indicator hsz
      simpa [indicator_supportOf] using this
    · intro x hx
      obtain ⟨hxL, hfx, hxa, hxb⟩ := Finset.mem_filter.mp hx
      have hcardx : (supportOf x).card = 3 := (Finset.mem_filter.mp hxL).2
      have haMem : a ∈ supportOf x := mem_supportOf.mpr hxa
      have hbNot : b ∉ supportOf x := by simp [hxb]
      let A : Finset (Fin 8) := Finset.univ.filter (fun i => φ i ∈ supportOf x)
      have hAimg : A.image φ = (supportOf x).erase a := by
        ext u
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, A]
        constructor
        · rintro ⟨i, hi, rfl⟩; exact ⟨hφ_ne_a i, hi⟩
        · rintro ⟨hua, hux⟩
          have huR : u ∈ R := by
            rw [Finset.mem_erase, Finset.mem_erase]
            refine ⟨?_, hua, Finset.mem_univ u⟩
            intro hub; subst hub; exact hbNot hux
          obtain ⟨i, rfl⟩ := hφ_surj u huR
          exact ⟨i, hux, rfl⟩
      have hAcard : A.card = 2 := by
        have := congrArg Finset.card hAimg
        rw [Finset.card_image_of_injective A hφ_inj, Finset.card_erase_of_mem haMem, hcardx] at this
        exact this
      have hlx : liftA (indicator A) = x := by
        simp only [liftA, supportOf_indicator, hAimg, Finset.insert_erase haMem, indicator_supportOf]
      refine ⟨indicator A, ?_, hlx⟩
      rw [Finset.mem_filter, hammingLayer, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _, by simp [hAcard]⟩, by rw [hlx]; exact hfx⟩
  have hcardB : ∑ z ∈ hammingLayer 8 2, boolToReal (f (liftB z)) =
      (((hammingLayer 10 3).filter (fun x => f x = true ∧ x b = true ∧ x a = false)).card : ℝ) := by
    simp only [boolToReal]
    rw [Finset.sum_boole]
    apply congrArg (Nat.cast : ℕ → ℝ)
    apply Finset.card_bij (fun z _ => liftB z)
    · intro z hz
      obtain ⟨hzL, hfz⟩ := Finset.mem_filter.mp hz
      rw [Finset.mem_filter]
      refine ⟨(h1_lift_mem 2 z hzL).2, hfz, ?_, ?_⟩
      · simp [liftB, indicator]
      · have haNot : a ∉ insert b ((supportOf z).image φ) := by
          simp only [Finset.mem_insert, Finset.mem_image, not_or, not_exists, not_and]
          exact ⟨hab, fun i _ => hφ_ne_a i⟩
        simp [liftB, indicator, haNot]
    · intro z₁ _ z₂ _ hEq
      have hsupp : insert b ((supportOf z₁).image φ) = insert b ((supportOf z₂).image φ) := by
        have := congrArg supportOf hEq
        simpa [liftB] using this
      have hb1 : b ∉ (supportOf z₁).image φ := by
        simp only [Finset.mem_image, not_exists, not_and]; intro i _; exact hφ_ne_b i
      have hb2 : b ∉ (supportOf z₂).image φ := by
        simp only [Finset.mem_image, not_exists, not_and]; intro i _; exact hφ_ne_b i
      have himg : (supportOf z₁).image φ = (supportOf z₂).image φ := by
        have := congrArg (fun S => S.erase b) hsupp
        simpa [Finset.erase_insert hb1, Finset.erase_insert hb2] using this
      have hsz : supportOf z₁ = supportOf z₂ := Finset.image_injective hφ_inj himg
      have := congrArg indicator hsz
      simpa [indicator_supportOf] using this
    · intro x hx
      obtain ⟨hxL, hfx, hxb, hxa⟩ := Finset.mem_filter.mp hx
      have hcardx : (supportOf x).card = 3 := (Finset.mem_filter.mp hxL).2
      have hbMem : b ∈ supportOf x := mem_supportOf.mpr hxb
      have haNot : a ∉ supportOf x := by simp [hxa]
      let A : Finset (Fin 8) := Finset.univ.filter (fun i => φ i ∈ supportOf x)
      have hAimg : A.image φ = (supportOf x).erase b := by
        ext u
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, A]
        constructor
        · rintro ⟨i, hi, rfl⟩; exact ⟨hφ_ne_b i, hi⟩
        · rintro ⟨hub, hux⟩
          have huR : u ∈ R := by
            rw [Finset.mem_erase, Finset.mem_erase]
            refine ⟨hub, ?_, Finset.mem_univ u⟩
            intro hua; subst hua; exact haNot hux
          obtain ⟨i, rfl⟩ := hφ_surj u huR
          exact ⟨i, hux, rfl⟩
      have hAcard : A.card = 2 := by
        have := congrArg Finset.card hAimg
        rw [Finset.card_image_of_injective A hφ_inj, Finset.card_erase_of_mem hbMem, hcardx] at this
        exact this
      have hlx : liftB (indicator A) = x := by
        simp only [liftB, supportOf_indicator, hAimg, Finset.insert_erase hbMem, indicator_supportOf]
      refine ⟨indicator A, ?_, hlx⟩
      rw [Finset.mem_filter, hammingLayer, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _, by simp [hAcard]⟩, by rw [hlx]; exact hfx⟩
  have hdiff : ((hammingLayer 10 3).filter (fun x => f x = true ∧ x a = true ∧ x b = false)).card =
      ((hammingLayer 10 3).filter (fun x => f x = true ∧ x b = true ∧ x a = false)).card := by
    have hsub : ∑ z ∈ hammingLayer 8 2, boolToReal (f (liftA z)) -
        ∑ z ∈ hammingLayer 8 2, boolToReal (f (liftB z)) = 0 := by
      rw [← Finset.sum_sub_distrib]
      exact hsum2
    rw [hcardA, hcardB] at hsub
    have hR : (((hammingLayer 10 3).filter (fun x => f x = true ∧ x a = true ∧ x b = false)).card : ℝ) =
        (((hammingLayer 10 3).filter (fun x => f x = true ∧ x b = true ∧ x a = false)).card : ℝ) := by
      linarith
    exact_mod_cast hR
  have hsplitA : layer3Deg f a =
      ((hammingLayer 10 3).filter (fun x => f x = true ∧ x a = true ∧ x b = false)).card +
      layer3Codeg f a b := by
    rw [layer3Deg, layer3Codeg, ← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_union]
      cases hxb : x b <;> simp
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 := (Finset.mem_filter.mp hx1).2.2.2
      have h2 := (Finset.mem_filter.mp hx2).2.2.2
      rw [h1] at h2; exact Bool.false_ne_true h2
  have hsplitB : layer3Deg f b =
      ((hammingLayer 10 3).filter (fun x => f x = true ∧ x b = true ∧ x a = false)).card +
      layer3Codeg f a b := by
    rw [layer3Deg, layer3Codeg_comm f a b, layer3Codeg, ← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_union]
      cases hxa : x a <;> simp
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 := (Finset.mem_filter.mp hx1).2.2.2
      have h2 := (Finset.mem_filter.mp hx2).2.2.2
      rw [h1] at h2; exact Bool.false_ne_true h2
  omega

/-! ### Step 3: Codegree quadrangle identity `d(a, c) + d(b, d) = d(a, d) + d(b, c)` -/

private lemma deg4_dim10_step3 {f : BooleanFun 10} (hf : polyDegree f ≤ 4)
    (hf_l2 : ∀ x ∈ hammingLayer 10 2, f x = true)
    (hf_l5 : ∀ x ∈ hammingLayer 10 5, f x = false)
    (hf_l8 : ∀ x ∈ hammingLayer 10 8, f x = true)
    {a b c d : Fin 10}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    layer3Codeg f a c + layer3Codeg f b d = layer3Codeg f a d + layer3Codeg f b c := by
  classical
  let R2 : Finset (Fin 10) := (((Finset.univ.erase a).erase b).erase c).erase d
  have hR2card : R2.card = 6 := by
    have hb1 : b ∈ (Finset.univ : Finset (Fin 10)).erase a :=
      Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ _⟩
    have hc1 : c ∈ ((Finset.univ : Finset (Fin 10)).erase a).erase b :=
      Finset.mem_erase.mpr ⟨Ne.symm hbc, Finset.mem_erase.mpr ⟨Ne.symm hac, Finset.mem_univ _⟩⟩
    have hd1 : d ∈ (((Finset.univ : Finset (Fin 10)).erase a).erase b).erase c :=
      Finset.mem_erase.mpr ⟨Ne.symm hcd, Finset.mem_erase.mpr ⟨Ne.symm hbd,
        Finset.mem_erase.mpr ⟨Ne.symm had, Finset.mem_univ _⟩⟩⟩
    rw [Finset.card_erase_of_mem hd1, Finset.card_erase_of_mem hc1,
      Finset.card_erase_of_mem hb1, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin]
  let eR2 : Fin 6 ≃ R2 := (Fintype.equivFinOfCardEq (by simp [hR2card])).symm
  let ψ : Fin 6 → Fin 10 := fun i => (eR2 i).1
  have hψ_inj : Function.Injective ψ := fun i₁ i₂ h => eR2.injective (Subtype.ext h)
  have hψ_ne : ∀ i : Fin 6, ψ i ≠ a ∧ ψ i ≠ b ∧ ψ i ≠ c ∧ ψ i ≠ d := by
    intro i
    have hi := (eR2 i).2
    simp only [R2, Finset.mem_erase, Finset.mem_univ, and_true] at hi
    exact ⟨hi.2.2.2, hi.2.2.1, hi.2.1, hi.1⟩
  let pairLift (u v : Fin 10) (y : Fin 6 → Bool) : Fin 10 → Bool :=
    indicator (insert u (insert v ((supportOf y).image ψ)))
  let h2 : (Fin 6 → Bool) → ℝ := fun y =>
    boolToReal (f (pairLift a c y)) - boolToReal (f (pairLift a d y)) -
    boolToReal (f (pairLift b c y)) + boolToReal (f (pairLift b d y))
  let c2 : Finset (Fin 6) → ℝ := fun T =>
    (mobiusCoeff f (insert a (insert c (T.image ψ))) : ℝ) -
    (mobiusCoeff f (insert a (insert d (T.image ψ))) : ℝ) -
    (mobiusCoeff f (insert b (insert c (T.image ψ))) : ℝ) +
    (mobiusCoeff f (insert b (insert d (T.image ψ))) : ℝ)
  have hnot_img : ∀ (S : Finset (Fin 6)),
      a ∉ S.image ψ ∧ b ∉ S.image ψ ∧ c ∉ S.image ψ ∧ d ∉ S.image ψ := by
    intro S
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [Finset.mem_image, not_exists, not_and]
      intro i _
      have := hψ_ne i
      tauto
  have h2_rep : ∀ y : Fin 6 → Bool, ∑ T ∈ (supportOf y).powerset, c2 T = h2 y := by
    intro y
    obtain ⟨haN, hbN, hcN, hdN⟩ := hnot_img (supportOf y)
    let A := (supportOf y).image ψ
    have ha_c : a ∉ insert c A := by simp [A, hac, haN]
    have ha_d : a ∉ insert d A := by simp [A, had, haN]
    have hb_c : b ∉ insert c A := by simp [A, hbc, hbN]
    have hb_d : b ∉ insert d A := by simp [A, hbd, hbN]
    have hAC := sum_mobius_powerset f (insert a (insert c A))
    have hAD := sum_mobius_powerset f (insert a (insert d A))
    have hBC := sum_mobius_powerset f (insert b (insert c A))
    have hBD := sum_mobius_powerset f (insert b (insert d A))
    rw [sum_powerset_insert _ ha_c, sum_powerset_insert _ hcN,
        sum_powerset_insert _ hcN] at hAC
    rw [sum_powerset_insert _ ha_d, sum_powerset_insert _ hdN,
        sum_powerset_insert _ hdN] at hAD
    rw [sum_powerset_insert _ hb_c, sum_powerset_insert _ hcN,
        sum_powerset_insert _ hcN] at hBC
    rw [sum_powerset_insert _ hb_d, sum_powerset_insert _ hdN,
        sum_powerset_insert _ hdN] at hBD
    have hcomb : h2 y = ∑ T ∈ A.powerset,
        ((mobiusCoeff f (insert a (insert c T)) : ℝ) -
         (mobiusCoeff f (insert a (insert d T)) : ℝ) -
         (mobiusCoeff f (insert b (insert c T)) : ℝ) +
         (mobiusCoeff f (insert b (insert d T)) : ℝ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      change boolToReal (f (indicator (insert a (insert c A)))) -
        boolToReal (f (indicator (insert a (insert d A)))) -
        boolToReal (f (indicator (insert b (insert c A)))) +
        boolToReal (f (indicator (insert b (insert d A)))) = _
      linarith
    rw [hcomb]
    exact (sum_powerset_image ψ hψ_inj (supportOf y)
      (fun T => (mobiusCoeff f (insert a (insert c T)) : ℝ) -
                (mobiusCoeff f (insert a (insert d T)) : ℝ) -
                (mobiusCoeff f (insert b (insert c T)) : ℝ) +
                (mobiusCoeff f (insert b (insert d T)) : ℝ))).symm
  have h2_deg : ∀ T : Finset (Fin 6), 2 < T.card → c2 T = 0 := by
    intro T hT
    obtain ⟨haN, hbN, hcN, hdN⟩ := hnot_img T
    have hm_zero : ∀ u v : Fin 10, u ≠ v → u ∉ T.image ψ → v ∉ T.image ψ →
        mobiusCoeff f (insert u (insert v (T.image ψ))) = 0 := by
      intro u v huv huN hvN
      apply mobiusCoeff_eq_zero_of_polyDegree_lt
      have huN' : u ∉ insert v (T.image ψ) := by simp [huv, huN]
      rw [Finset.card_insert_of_notMem huN', Finset.card_insert_of_notMem hvN,
        Finset.card_image_of_injective T hψ_inj]
      omega
    simp [c2, hm_zero a c hac haN hcN, hm_zero a d had haN hdN,
      hm_zero b c hbc hbN hcN, hm_zero b d hbd hbN hdN]
  have h2_lift_mem : ∀ (u v : Fin 10), u ≠ v →
      (∀ i, ψ i ≠ u) → (∀ i, ψ i ≠ v) →
      ∀ (r : ℕ) (y : Fin 6 → Bool), y ∈ hammingLayer 6 r →
        pairLift u v y ∈ hammingLayer 10 (r + 2) := by
    intro u v huv hu hv r y hy
    have hrc : (supportOf y).card = r := (Finset.mem_filter.mp hy).2
    have hvN : v ∉ (supportOf y).image ψ := by
      simp only [Finset.mem_image, not_exists, not_and]; intro i _; exact hv i
    have huN : u ∉ insert v ((supportOf y).image ψ) := by
      simp only [Finset.mem_insert, Finset.mem_image, not_or, not_exists, not_and]
      exact ⟨huv, fun i _ => hu i⟩
    rw [hammingLayer, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by
      simp [pairLift, Finset.card_insert_of_notMem huN, Finset.card_insert_of_notMem hvN,
        Finset.card_image_of_injective _ hψ_inj, hrc]⟩
  have h2_zero_layer : ∀ r : ℕ, (∀ x ∈ hammingLayer 10 (r + 2), f x = true) ∨
      (∀ x ∈ hammingLayer 10 (r + 2), f x = false) → layerAvg h2 r = 0 := by
    intro r hconst
    rw [layerAvg, realLayerSum]
    have hsum0 : ∑ y ∈ hammingLayer 6 r, h2 y = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      have hAC := h2_lift_mem a c hac (fun i => (hψ_ne i).1) (fun i => (hψ_ne i).2.2.1) r y hy
      have hAD := h2_lift_mem a d had (fun i => (hψ_ne i).1) (fun i => (hψ_ne i).2.2.2) r y hy
      have hBC := h2_lift_mem b c hbc (fun i => (hψ_ne i).2.1) (fun i => (hψ_ne i).2.2.1) r y hy
      have hBD := h2_lift_mem b d hbd (fun i => (hψ_ne i).2.1) (fun i => (hψ_ne i).2.2.2) r y hy
      rcases hconst with ht | hff
      · simp [h2, ht _ hAC, ht _ hAD, ht _ hBC, ht _ hBD]
      · simp [h2, hff _ hAC, hff _ hAD, hff _ hBC, hff _ hBD]
    rw [hsum0, zero_div]
  have h2_0 : layerAvg h2 0 = 0 := h2_zero_layer 0 (Or.inl hf_l2)
  have h2_3 : layerAvg h2 3 = 0 := h2_zero_layer 3 (Or.inr hf_l5)
  have h2_6 : layerAvg h2 6 = 0 := h2_zero_layer 6 (Or.inl hf_l8)
  have hid_h2 := symmetrisation_linear_identity h2 c2 h2_rep h2_deg
    ![5, -9, 0, 5, 0, 0, -1] (by decide)
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one] at hid_h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ,
    Int.cast_neg, Int.cast_ofNat, Int.cast_zero, Int.cast_one, zero_mul, zero_add] at hid_h2
  have h2_1 : layerAvg h2 1 = 0 := by linarith
  have hsum1 : realLayerSum h2 1 = 0 := by
    rw [layerAvg] at h2_1
    have hch : (Nat.choose 6 1 : ℝ) ≠ 0 := by exact_mod_cast (by decide : Nat.choose 6 1 ≠ 0)
    exact (div_eq_zero_iff.mp h2_1).resolve_right hch
  have hsum_R2 : ∀ (u v : Fin 10),
      ∑ y ∈ hammingLayer 6 1, boolToReal (f (pairLift u v y)) =
        ∑ w ∈ R2, boolToReal (f (indicator {u, v, w})) := by
    intro u v
    have h1 : ∑ y ∈ hammingLayer 6 1, boolToReal (f (pairLift u v y)) =
        ∑ i : Fin 6, boolToReal (f (indicator {u, v, ψ i})) := by
      symm
      apply Finset.sum_nbij (fun i => basisVec i)
      · intro i _
        rw [hammingLayer, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hsupp : supportOf (basisVec i) = {i} := by ext j; simp [basisVec_apply]
        rw [hsupp, Finset.card_singleton]
      · intro i₁ _ i₂ _ hEq
        have h := congrFun hEq i₁
        simp only [basisVec_apply, decide_true] at h
        exact of_decide_eq_true h.symm
      · intro y hy
        have hcardy : (supportOf y).card = 1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcardy
        refine ⟨i, Finset.mem_coe.mpr (Finset.mem_univ i), ?_⟩
        have hsupp : supportOf (basisVec i) = supportOf y := by
          rw [hi]; ext j; simp [basisVec_apply]
        have := congrArg indicator hsupp
        simpa [indicator_supportOf] using this
      · intro i _
        have hsupp : supportOf (basisVec i) = {i} := by ext j; simp [basisVec_apply]
        simp only [pairLift, hsupp, Finset.image_singleton]
    rw [h1]
    apply Finset.sum_nbij ψ
    · intro i _; exact (eR2 i).2
    · intro i₁ _ i₂ _ hEq; exact hψ_inj hEq
    · intro w hw
      have hw' : w ∈ R2 := Finset.mem_coe.mp hw
      exact ⟨eR2.symm ⟨w, hw'⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by simp [ψ]⟩
    · intro _ _; rfl
  have hcodeg_sum : ∀ (u v : Fin 10), u ≠ v →
      (layer3Codeg f u v : ℝ) =
        ∑ w ∈ (Finset.univ.erase u).erase v, boolToReal (f (indicator {u, v, w})) := by
    intro u v huv
    simp only [boolToReal]
    rw [Finset.sum_boole]
    apply congrArg (Nat.cast : ℕ → ℝ)
    rw [layer3Codeg]
    symm
    apply Finset.card_bij (fun w _ => indicator {u, v, w})
    · intro w hw
      obtain ⟨hwR, hfw⟩ := Finset.mem_filter.mp hw
      have hwu : w ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hwR).2).1
      have hwv : w ≠ v := (Finset.mem_erase.mp hwR).1
      rw [Finset.mem_filter, hammingLayer, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, ?_⟩, hfw, ?_, ?_⟩
      · rw [supportOf_indicator]
        have huN : u ∉ ({v, w} : Finset (Fin 10)) := by simp [huv, Ne.symm hwu]
        have hvN : v ∉ ({w} : Finset (Fin 10)) := by simp [Ne.symm hwv]
        rw [Finset.card_insert_of_notMem huN, Finset.card_insert_of_notMem hvN,
          Finset.card_singleton]
      · simp [indicator]
      · simp [indicator]
    · intro w₁ hw₁ w₂ hw₂ hEq
      have h1R := (Finset.mem_filter.mp hw₁).1
      have hw1u : w₁ ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp h1R).2).1
      have hw1v : w₁ ≠ v := (Finset.mem_erase.mp h1R).1
      have hsupp : ({u, v, w₁} : Finset (Fin 10)) = {u, v, w₂} := by
        have := congrArg supportOf hEq
        simpa using this
      have hmem : w₁ ∈ ({u, v, w₂} : Finset (Fin 10)) := by rw [← hsupp]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact absurd rfl hw1u
      · exact absurd rfl hw1v
      · rfl
    · intro x hx
      obtain ⟨hxL, hfx, hxu, hxv⟩ := Finset.mem_filter.mp hx
      have hcardx : (supportOf x).card = 3 := (Finset.mem_filter.mp hxL).2
      have huM : u ∈ supportOf x := mem_supportOf.mpr hxu
      have hvM : v ∈ (supportOf x).erase u := Finset.mem_erase.mpr ⟨Ne.symm huv, mem_supportOf.mpr hxv⟩
      have hcard1 : (((supportOf x).erase u).erase v).card = 1 := by
        rw [Finset.card_erase_of_mem hvM, Finset.card_erase_of_mem huM, hcardx]
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
      have hwMem : w ∈ ((supportOf x).erase u).erase v := by rw [hw]; exact Finset.mem_singleton_self w
      have hwv : w ≠ v := (Finset.mem_erase.mp hwMem).1
      have hwu : w ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hwMem).2).1
      have hsupp : ({u, v, w} : Finset (Fin 10)) = supportOf x := by
        have h1 : insert v ({w} : Finset (Fin 10)) = (supportOf x).erase u := by
          rw [← hw, Finset.insert_erase hvM]
        rw [h1, Finset.insert_erase huM]
      have hind : indicator {u, v, w} = x := by rw [hsupp, indicator_supportOf]
      refine ⟨w, Finset.mem_filter.mpr ⟨?_, by rw [hind]; exact hfx⟩, hind⟩
      exact Finset.mem_erase.mpr ⟨hwv, Finset.mem_erase.mpr ⟨hwu, Finset.mem_univ w⟩⟩
  have hR2_not : a ∉ R2 ∧ b ∉ R2 ∧ c ∉ R2 ∧ d ∉ R2 := by simp [R2]
  have hsplit_ac : (Finset.univ.erase a).erase c = insert b (insert d R2) := by
    ext w
    simp only [R2, Finset.mem_erase, Finset.mem_insert, Finset.mem_univ, and_true]
    by_cases hwb : w = b
    · subst hwb; simp [Ne.symm hab, hbc]
    · by_cases hwd : w = d
      · subst hwd; simp [Ne.symm had, Ne.symm hcd]
      · simp [hwb, hwd]
  have hsplit_ad : (Finset.univ.erase a).erase d = insert b (insert c R2) := by
    ext w
    simp only [R2, Finset.mem_erase, Finset.mem_insert, Finset.mem_univ, and_true]
    by_cases hwb : w = b
    · subst hwb; simp [Ne.symm hab, hbd]
    · by_cases hwc : w = c
      · subst hwc; simp [Ne.symm hac, hcd]
      · simp [hwb, hwc]
  have hsplit_bc : (Finset.univ.erase b).erase c = insert a (insert d R2) := by
    ext w
    simp only [R2, Finset.mem_erase, Finset.mem_insert, Finset.mem_univ, and_true]
    by_cases hwa : w = a
    · subst hwa; simp [hab, hac]
    · by_cases hwd : w = d
      · subst hwd; simp [Ne.symm hbd, Ne.symm hcd]
      · simp [hwa, hwd]
  have hsplit_bd : (Finset.univ.erase b).erase d = insert a (insert c R2) := by
    ext w
    simp only [R2, Finset.mem_erase, Finset.mem_insert, Finset.mem_univ, and_true]
    by_cases hwa : w = a
    · subst hwa; simp [hab, had]
    · by_cases hwc : w = c
      · subst hwc; simp [Ne.symm hbc, hcd]
      · simp [hwa, hwc]
  have hac_eq := hcodeg_sum a c hac
  have had_eq := hcodeg_sum a d had
  have hbc_eq := hcodeg_sum b c hbc
  have hbd_eq := hcodeg_sum b d hbd
  rw [hsplit_ac, Finset.sum_insert (by simp [hbd, hR2_not.2.1]),
    Finset.sum_insert hR2_not.2.2.2] at hac_eq
  rw [hsplit_ad, Finset.sum_insert (by simp [hbc, hR2_not.2.1]),
    Finset.sum_insert hR2_not.2.2.1] at had_eq
  rw [hsplit_bc, Finset.sum_insert (by simp [had, hR2_not.1]),
    Finset.sum_insert hR2_not.2.2.2] at hbc_eq
  rw [hsplit_bd, Finset.sum_insert (by simp [hac, hR2_not.1]),
    Finset.sum_insert hR2_not.2.2.1] at hbd_eq
  have ht1 : ({a, c, b} : Finset (Fin 10)) = {b, c, a} := by
    rw [Finset.insert_comm a c, Finset.pair_comm a b, Finset.insert_comm c b]
  have ht2 : ({a, c, d} : Finset (Fin 10)) = {a, d, c} := by
    rw [Finset.pair_comm c d]
  have ht3 : ({a, d, b} : Finset (Fin 10)) = {b, d, a} := by
    rw [Finset.insert_comm a d, Finset.pair_comm a b, Finset.insert_comm d b]
  have ht4 : ({b, c, d} : Finset (Fin 10)) = {b, d, c} := by
    rw [Finset.pair_comm c d]
  rw [ht1, ht2] at hac_eq
  rw [ht3] at had_eq
  rw [ht4] at hbc_eq
  have hsum1_exp : ∑ w ∈ R2, boolToReal (f (indicator {a, c, w})) -
      ∑ w ∈ R2, boolToReal (f (indicator {a, d, w})) -
      ∑ w ∈ R2, boolToReal (f (indicator {b, c, w})) +
      ∑ w ∈ R2, boolToReal (f (indicator {b, d, w})) = 0 := by
    rw [← hsum_R2 a c, ← hsum_R2 a d, ← hsum_R2 b c, ← hsum_R2 b d]
    have : realLayerSum h2 1 =
        ∑ y ∈ hammingLayer 6 1, boolToReal (f (pairLift a c y)) -
        ∑ y ∈ hammingLayer 6 1, boolToReal (f (pairLift a d y)) -
        ∑ y ∈ hammingLayer 6 1, boolToReal (f (pairLift b c y)) +
        ∑ y ∈ hammingLayer 6 1, boolToReal (f (pairLift b d y)) := by
      simp only [realLayerSum, h2, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    linarith
  have hR : (layer3Codeg f a c : ℝ) + (layer3Codeg f b d : ℝ) =
      (layer3Codeg f a d : ℝ) + (layer3Codeg f b c : ℝ) := by
    linarith
  exact_mod_cast hR

/-! ### Step 4: Divisibility contradiction (`90 * K = 420`) -/

/-- No normalized 10-bit Boolean function of degree `≤ 4` exists. -/
theorem no_normalized_deg4_dim10 :
    ¬ ∃ f : BooleanFun 10, polyDegree f ≤ 4 ∧ f (zeroVec 10) = false ∧
      ∀ i : Fin 10, f (basisVec i) = true := by
  classical
  rintro ⟨f, hf, hf0, hf1⟩
  obtain ⟨hf_l1, hf_l2, hf_l5, hf_l8, hS3⟩ := deg4_dim10_step1 hf hf0 hf1
  have hdeg_eq : ∀ a b : Fin 10, layer3Deg f a = layer3Deg f b :=
    deg4_dim10_step2 hf hf_l1 hf_l2 hf_l5 hf_l8
  have hcodeg_eq_of_common : ∀ a b c : Fin 10, a ≠ b → a ≠ c → b ≠ c →
      layer3Codeg f a c = layer3Codeg f b c := by
    intro a b c hab hac hbc
    let S3 : Finset (Fin 10) := ((Finset.univ.erase a).erase b).erase c
    have hS3card : S3.card = 7 := by
      have hb1 : b ∈ (Finset.univ : Finset (Fin 10)).erase a :=
        Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ _⟩
      have hc1 : c ∈ ((Finset.univ : Finset (Fin 10)).erase a).erase b :=
        Finset.mem_erase.mpr ⟨Ne.symm hbc, Finset.mem_erase.mpr ⟨Ne.symm hac, Finset.mem_univ _⟩⟩
      rw [Finset.card_erase_of_mem hc1, Finset.card_erase_of_mem hb1,
        Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    have hsum_quad : ∑ d ∈ S3, (layer3Codeg f a c + layer3Codeg f b d) =
        ∑ d ∈ S3, (layer3Codeg f a d + layer3Codeg f b c) := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [S3, Finset.mem_erase, Finset.mem_univ, and_true] at hd
      exact deg4_dim10_step3 hf hf_l2 hf_l5 hf_l8 hab hac (Ne.symm hd.2.2) hbc
        (Ne.symm hd.2.1) (Ne.symm hd.1)
    simp only [Finset.sum_add_distrib, Finset.sum_const, hS3card, smul_eq_mul] at hsum_quad
    have ha_erase : Finset.univ.erase a = insert b (insert c S3) := by
      ext d
      simp only [S3, Finset.mem_erase, Finset.mem_insert, Finset.mem_univ, and_true]
      by_cases hdb : d = b
      · subst hdb; simp [Ne.symm hab]
      · by_cases hdc : d = c
        · subst hdc; simp [Ne.symm hac]
        · simp [hdb, hdc]
    have hb_erase : Finset.univ.erase b = insert a (insert c S3) := by
      ext d
      simp only [S3, Finset.mem_erase, Finset.mem_insert, Finset.mem_univ, and_true]
      by_cases hda : d = a
      · subst hda; simp [hab]
      · by_cases hdc : d = c
        · subst hdc; simp [Ne.symm hbc]
        · simp [hda, hdc]
    have hS3_not : a ∉ S3 ∧ b ∉ S3 ∧ c ∉ S3 := by simp [S3]
    have hdegA := sum_layer3Codeg_erase f a
    have hdegB := sum_layer3Codeg_erase f b
    rw [ha_erase, Finset.sum_insert (by simp [hbc, hS3_not.2.1]),
      Finset.sum_insert hS3_not.2.2] at hdegA
    rw [hb_erase, Finset.sum_insert (by simp [hac, hS3_not.1]),
      Finset.sum_insert hS3_not.2.2] at hdegB
    have hDAB : layer3Deg f a = layer3Deg f b := hdeg_eq a b
    have hcomm : layer3Codeg f a b = layer3Codeg f b a := layer3Codeg_comm f a b
    omega
  let K : ℕ := layer3Codeg f 0 1
  have hcodeg_const : ∀ u v : Fin 10, u ≠ v → layer3Codeg f u v = K := by
    intro u v huv
    by_cases hv0 : v = 0
    · subst hv0
      by_cases hu1 : u = 1
      · subst hu1; exact layer3Codeg_comm f 1 0
      · calc layer3Codeg f u 0 = layer3Codeg f 1 0 :=
              hcodeg_eq_of_common u 1 0 hu1 huv (by decide)
          _ = K := layer3Codeg_comm f 1 0
    · have h1 : layer3Codeg f u v = layer3Codeg f 0 v := by
        by_cases hu0 : u = 0
        · subst hu0; rfl
        · exact hcodeg_eq_of_common u 0 v hu0 huv (Ne.symm hv0)
      rw [h1, layer3Codeg_comm f 0 v]
      by_cases hv1 : v = 1
      · subst hv1; exact layer3Codeg_comm f 1 0
      · calc layer3Codeg f v 0 = layer3Codeg f 1 0 :=
              hcodeg_eq_of_common v 1 0 hv1 hv0 (by decide)
          _ = K := layer3Codeg_comm f 1 0
  have htotal_lhs : ∑ u : Fin 10, ∑ v ∈ Finset.univ.erase u, layer3Codeg f u v = 90 * K := by
    calc ∑ u : Fin 10, ∑ v ∈ Finset.univ.erase u, layer3Codeg f u v
        = ∑ u : Fin 10, ∑ _v ∈ Finset.univ.erase u, K := by
          apply Finset.sum_congr rfl
          intro u _
          apply Finset.sum_congr rfl
          intro v hv
          exact hcodeg_const u v (Ne.symm (Finset.mem_erase.mp hv).1)
      _ = ∑ u : Fin 10, 9 * K := by
          apply Finset.sum_congr rfl
          intro u _
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ u),
            Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ = 90 * K := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring
  have htotal_rhs : ∑ u : Fin 10, ∑ v ∈ Finset.univ.erase u, layer3Codeg f u v = 420 := by
    calc ∑ u : Fin 10, ∑ v ∈ Finset.univ.erase u, layer3Codeg f u v
        = ∑ u : Fin 10, 2 * layer3Deg f u := by
          apply Finset.sum_congr rfl
          intro u _
          exact sum_layer3Codeg_erase f u
      _ = 2 * ∑ u : Fin 10, layer3Deg f u := (Finset.mul_sum _ _ _).symm
      _ = 2 * (3 * boolLayerSum f 3) := by rw [sum_layer3Deg]
      _ = 420 := by rw [hS3]
  omega

/-- **Sharp Degree-4 Sensitivity Upper Bound**:
Every Boolean function `f` of real degree `≤ 4` on ANY number of variables
satisfies `maxSensitivity f ≤ 9` (matching `NAE₃ ∘ NAE₃`). -/
theorem maxSensitivity_le_nine_of_deg_le_four_proof :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 4 → maxSensitivity f ≤ 9 := by
  intro n f hf
  have h := maxSensitivity_lt_of_no_normalized no_normalized_deg4_dim10 n f hf
  omega

end DegreeSensitivity
