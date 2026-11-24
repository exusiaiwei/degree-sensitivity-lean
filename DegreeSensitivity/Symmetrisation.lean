module

public import DegreeSensitivity.Sensitivity
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Symmetrisation Lemma and Exact Farkas LP Certificate Engine

We prove the Minsky–Papert / Nisan–Szegedy Symmetrisation Lemma for arbitrary
real-valued functions `g : {0, 1}^m → ℝ` of multilinear degree `≤ d`:
the layer averages `layerAvg g k = E_{|x| = k}[g(x)]` are an exact linear
combination of the binomial polynomials `k ↦ Nat.choose k j` for `0 ≤ j ≤ d`,
hence coincide on `{0, ..., m}` with a univariate polynomial `q : ℝ[X]` of
degree `≤ d`.

As immediate corollaries we obtain:
1. A reusable exact integer **Farkas LP Certificate Engine** proving
   `maxSensitivity f < n` whenever `y : Fin (n + 1) → ℤ` satisfies
   `∑ k, y k * C(k, j) = 0` for all `j ≤ d` and `y 1 > ∑_{k ≥ 2, y k < 0} (-y k)`.
2. One-line proofs of the exact Wellens LP bounds for `d = 2, 3, 4, 5, 6`.
-/

namespace DegreeSensitivity

open scoped BigOperators
open Polynomial

/-- The Hamming layer `L_k = { x : Fin m → Bool | |supportOf x| = k }`. -/
def hammingLayer (m k : ℕ) : Finset (Fin m → Bool) :=
  Finset.univ.filter (fun x : Fin m → Bool => (supportOf x).card = k)

lemma card_hammingLayer (m k : ℕ) : (hammingLayer m k).card = Nat.choose m k := by
  classical
  have hbij : (hammingLayer m k).card =
      (Finset.powersetCard k (Finset.univ : Finset (Fin m))).card := by
    apply Finset.card_bij (fun x _ => supportOf x)
    · intro x hx
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, (Finset.mem_filter.mp hx).2⟩
    · intro x₁ _ x₂ _ hEq
      have := congrArg indicator hEq
      simpa [indicator_supportOf] using this
    · intro S hS
      refine ⟨indicator S, ?_, supportOf_indicator S⟩
      rw [hammingLayer, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [supportOf_indicator]; exact (Finset.mem_powersetCard.mp hS).2⟩
  rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- Count of weight-`k` bitstrings whose support contains a given subset `S`. -/
lemma card_hammingLayer_filter_subset {m : ℕ} (S : Finset (Fin m)) (k : ℕ) :
    ((hammingLayer m k).filter (fun x => S ⊆ supportOf x)).card =
      if S.card ≤ k then Nat.choose (m - S.card) (k - S.card) else 0 := by
  classical
  by_cases hle : S.card ≤ k
  · simp only [hle, ↓reduceIte]
    have hbij : ((hammingLayer m k).filter (fun x => S ⊆ supportOf x)).card =
        (Finset.powersetCard (k - S.card) Sᶜ).card := by
      apply Finset.card_bij (fun x _ => supportOf x \ S)
      · intro x hx
        obtain ⟨hxL, hSx⟩ := Finset.mem_filter.mp hx
        have hcardx : (supportOf x).card = k := (Finset.mem_filter.mp hxL).2
        rw [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro i hi
          rw [Finset.mem_sdiff] at hi
          simp [hi.2]
        · rw [Finset.card_sdiff_of_subset hSx, hcardx]
      · intro x₁ hx₁ x₂ hx₂ hEq
        have h1 : S ⊆ supportOf x₁ := (Finset.mem_filter.mp hx₁).2
        have h2 : S ⊆ supportOf x₂ := (Finset.mem_filter.mp hx₂).2
        have hsupp : supportOf x₁ = supportOf x₂ := by
          rw [← Finset.union_sdiff_of_subset h1, ← Finset.union_sdiff_of_subset h2, hEq]
        have := congrArg indicator hsupp
        simpa [indicator_supportOf] using this
      · intro R hR
        rw [Finset.mem_powersetCard] at hR
        obtain ⟨hRsub, hRcard⟩ := hR
        have hdisj : Disjoint S R := by
          rw [Finset.disjoint_left]
          intro i hiS hiR
          exact (Finset.mem_compl.mp (hRsub hiR)) hiS
        refine ⟨indicator (S ∪ R), ?_, ?_⟩
        · rw [Finset.mem_filter, hammingLayer, Finset.mem_filter]
          refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · rw [supportOf_indicator, Finset.card_union_of_disjoint hdisj, hRcard]
            omega
          · rw [supportOf_indicator]
            exact Finset.subset_union_left
        · rw [supportOf_indicator]
          exact Finset.union_sdiff_cancel_left hdisj
    rw [hbij, Finset.card_powersetCard, Finset.card_compl, Fintype.card_fin]
  · simp only [hle, ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx hSx
    have hcardx : (supportOf x).card = k := (Finset.mem_filter.mp hx).2
    have hle' : S.card ≤ (supportOf x).card := Finset.card_le_card hSx
    omega

/-- Binomial double-counting identity:
`(if j ≤ k then C(m - j, k - j) else 0) * C(m, j) = C(m, k) * C(k, j)` for `k ≤ m`. -/
lemma choose_sub_mul_choose {m k j : ℕ} (_hk : k ≤ m) :
    (if j ≤ k then Nat.choose (m - j) (k - j) else 0) * Nat.choose m j =
      Nat.choose m k * Nat.choose k j := by
  by_cases hj : j ≤ k
  · simp only [hj, ↓reduceIte]
    have hcm : m.choose k * k.choose j = m.choose j * (m - j).choose (k - j) := by
      have h1 := Nat.choose_mul (n := m) hj
      have h2 : (m - j).choose (k - j) = (m - j).choose (k - j) := rfl
      -- Wait: check symmetry if needed: `choose_mul hj` has `(m - j).choose (k - j)`
      simpa using h1
    linarith
  · simp only [hj, ↓reduceIte, zero_mul]
    rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hj), mul_zero]

/-- The layer sum `∑_{|x| = k} g(x)` of a real-valued function `g : {0, 1}^m → ℝ`. -/
noncomputable def realLayerSum {m : ℕ} (g : (Fin m → Bool) → ℝ) (k : ℕ) : ℝ :=
  ∑ x ∈ hammingLayer m k, g x

/-- The layer average `E_{|x| = k}[g(x)] = (1 / C(m, k)) ∑_{|x| = k} g(x)`. -/
noncomputable def layerAvg {m : ℕ} (g : (Fin m → Bool) → ℝ) (k : ℕ) : ℝ :=
  realLayerSum g k / (Nat.choose m k : ℝ)

/-- The integer layer sum `S_k = |{ x : |x| = k ∧ f x = true }|` of a Boolean function `f`. -/
def boolLayerSum {m : ℕ} (f : BooleanFun m) (k : ℕ) : ℕ :=
  ((hammingLayer m k).filter (fun x => f x = true)).card

lemma realLayerSum_bool {m : ℕ} (f : BooleanFun m) (k : ℕ) :
    realLayerSum (fun x => boolToReal (f x)) k = (boolLayerSum f k : ℝ) := by
  rw [realLayerSum, boolLayerSum]
  simp only [boolToReal]
  rw [Finset.sum_boole]

lemma layerAvg_bool_nonneg {m : ℕ} (f : BooleanFun m) (k : ℕ) :
    0 ≤ layerAvg (fun x => boolToReal (f x)) k := by
  rw [layerAvg, realLayerSum_bool]
  positivity

lemma layerAvg_bool_le_one {m : ℕ} (f : BooleanFun m) (k : ℕ) (hk : k ≤ m) :
    layerAvg (fun x => boolToReal (f x)) k ≤ 1 := by
  rw [layerAvg, realLayerSum_bool]
  have hpos : (0 : ℝ) < (Nat.choose m k : ℝ) := by
    exact_mod_cast Nat.choose_pos hk
  rw [div_le_one hpos]
  have hle : boolLayerSum f k ≤ Nat.choose m k := by
    calc boolLayerSum f k ≤ (hammingLayer m k).card := Finset.card_filter_le _ _
      _ = Nat.choose m k := card_hammingLayer m k
  exact_mod_cast hle

lemma layerAvg_bool_zero {m : ℕ} {f : BooleanFun m} (h0 : f (zeroVec m) = false) :
    layerAvg (fun x => boolToReal (f x)) 0 = 0 := by
  rw [layerAvg, realLayerSum, Nat.choose_zero_right, Nat.cast_one, div_one]
  apply Finset.sum_eq_zero
  intro x hx
  have hcard : (supportOf x).card = 0 := (Finset.mem_filter.mp hx).2
  have hsupp : supportOf x = ∅ := Finset.card_eq_zero.mp hcard
  have hx0 : x = zeroVec m := by
    funext i
    have hnot : i ∉ supportOf x := by rw [hsupp]; exact Finset.notMem_empty i
    cases hxi : x i
    · rfl
    · exact absurd (mem_supportOf.mpr hxi) hnot
  rw [hx0, h0]
  rfl

lemma layerAvg_bool_one {m : ℕ} {f : BooleanFun m} (hm : 1 ≤ m)
    (h1 : ∀ i : Fin m, f (basisVec i) = true) :
    layerAvg (fun x => boolToReal (f x)) 1 = 1 := by
  rw [layerAvg, realLayerSum]
  have hsum : ∑ x ∈ hammingLayer m 1, boolToReal (f x) = (hammingLayer m 1).card := by
    calc ∑ x ∈ hammingLayer m 1, boolToReal (f x)
        = ∑ _x ∈ hammingLayer m 1, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hcard : (supportOf x).card = 1 := (Finset.mem_filter.mp hx).2
          obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
          have hxb : x = basisVec i := by
            funext j
            rw [basisVec_apply]
            by_cases hji : j = i
            · subst hji
              have hmem : j ∈ supportOf x := by rw [hi]; exact Finset.mem_singleton_self j
              simp [mem_supportOf.mp hmem]
            · have hnot : j ∉ supportOf x := by rw [hi]; simp [hji]
              cases hxj : x j
              · simp [hji]
              · exact absurd (mem_supportOf.mpr hxj) hnot
          rw [hxb, h1 i]
          rfl
      _ = (hammingLayer m 1).card := by simp
  rw [hsum, card_hammingLayer]
  have hpos : (Nat.choose m 1 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hm).ne'
  exact div_self hpos

/-- **General Real Symmetrisation Theorem (Binomial Basis Form)**:
If `g : {0, 1}^m → ℝ` is represented by a multilinear polynomial `c` of degree `≤ d`,
then for every `k ≤ m`:
`layerAvg g k = ∑ j ∈ Finset.range (d + 1), a j * (Nat.choose k j : ℝ)`
where `a j = (∑_{|S| = j} c S) / C(m, j)`. -/
theorem layerAvg_eq_binomial_sum {m d : ℕ} (g : (Fin m → Bool) → ℝ)
    (c : Finset (Fin m) → ℝ)
    (hrep : ∀ x : Fin m → Bool, ∑ S ∈ (supportOf x).powerset, c S = g x)
    (hdeg : ∀ S : Finset (Fin m), d < S.card → c S = 0) :
    ∃ a : ℕ → ℝ, ∀ k ≤ m,
      layerAvg g k = ∑ j ∈ Finset.range (d + 1), a j * (Nat.choose k j : ℝ) := by
  classical
  let a : ℕ → ℝ := fun j =>
    (∑ S ∈ Finset.powersetCard j (Finset.univ : Finset (Fin m)), c S) / (Nat.choose m j : ℝ)
  refine ⟨a, fun k hk => ?_⟩
  rw [layerAvg, realLayerSum]
  have hsum : ∑ x ∈ hammingLayer m k, g x =
      ∑ S : Finset (Fin m),
        c S * (if S.card ≤ k then (Nat.choose (m - S.card) (k - S.card) : ℝ) else 0) := by
    calc ∑ x ∈ hammingLayer m k, g x
        = ∑ x ∈ hammingLayer m k, ∑ S : Finset (Fin m),
            if S ⊆ supportOf x then c S else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← hrep x, ← Finset.sum_filter]
          apply Finset.sum_congr _ (fun _ _ => rfl)
          ext S
          simp [Finset.mem_powerset]
      _ = ∑ S : Finset (Fin m), ∑ x ∈ hammingLayer m k,
            if S ⊆ supportOf x then c S else 0 := Finset.sum_comm
      _ = ∑ S : Finset (Fin m),
            c S * (((hammingLayer m k).filter (fun x => S ⊆ supportOf x)).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro S _
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ = ∑ S : Finset (Fin m),
            c S * (if S.card ≤ k then (Nat.choose (m - S.card) (k - S.card) : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro S _
          rw [card_hammingLayer_filter_subset]
          split_ifs <;> simp
  rw [hsum, div_eq_mul_inv, Finset.sum_mul]
  simp_rw [← div_eq_mul_inv]
  -- Partition `S : Finset (Fin m)` by `S.card` into `0 .. m`, and note terms with `S.card > d` vanish.
  have hfiber :
      ∑ S : Finset (Fin m),
        c S * (if S.card ≤ k then (Nat.choose (m - S.card) (k - S.card) : ℝ) else 0) /
          (Nat.choose m k : ℝ) =
      ∑ j ∈ Finset.range (d + 1),
        ∑ S ∈ Finset.powersetCard j (Finset.univ : Finset (Fin m)),
          c S * (if S.card ≤ k then (Nat.choose (m - S.card) (k - S.card) : ℝ) else 0) /
            (Nat.choose m k : ℝ) := by
    let F : Finset (Fin m) → ℝ := fun S =>
      c S * (if S.card ≤ k then (Nat.choose (m - S.card) (k - S.card) : ℝ) else 0) /
        (Nat.choose m k : ℝ)
    change ∑ S : Finset (Fin m), F S =
      ∑ j ∈ Finset.range (d + 1), ∑ S ∈ Finset.powersetCard j Finset.univ, F S
    have hsplit : ∑ S : Finset (Fin m), F S =
        ∑ j ∈ Finset.range (max m d + 1),
          ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => S.card = j), F S := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card)
        (t := Finset.range (max m d + 1))]
      intro S _
      rw [Finset.mem_range]
      have hcard : S.card ≤ m := by simpa using Finset.card_le_univ S
      omega
    rw [hsplit]
    have hsub : Finset.range (d + 1) ⊆ Finset.range (max m d + 1) :=
      Finset.range_mono (by omega)
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext S
      simp [Finset.mem_powersetCard]
    · intro j _ hjnot
      rw [Finset.mem_range] at hjnot
      apply Finset.sum_eq_zero
      intro S hS
      have hScard : S.card = j := (Finset.mem_filter.mp hS).2
      have hgt : d < S.card := by omega
      simp [F, hdeg S hgt]
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hjm : j ≤ m
  · have hmk_pos : (Nat.choose m k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
    have hmj_pos : (Nat.choose m j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjm).ne'
    have hratio : (if j ≤ k then (Nat.choose (m - j) (k - j) : ℝ) else 0) / (Nat.choose m k : ℝ) =
        (Nat.choose k j : ℝ) / (Nat.choose m j : ℝ) := by
      rw [div_eq_div_iff hmk_pos hmj_pos]
      have hid := choose_sub_mul_choose (m := m) (k := k) (j := j) hk
      have hidR : ((if j ≤ k then Nat.choose (m - j) (k - j) else 0 : ℕ) : ℝ) *
          (Nat.choose m j : ℝ) = (Nat.choose m k : ℝ) * (Nat.choose k j : ℝ) := by
        exact_mod_cast hid
      rw [mul_comm (Nat.choose k j : ℝ)]
      convert hidR using 2
      split_ifs <;> simp
    have hterm : ∀ S ∈ Finset.powersetCard j (Finset.univ : Finset (Fin m)),
        c S * (if S.card ≤ k then (Nat.choose (m - S.card) (k - S.card) : ℝ) else 0) /
          (Nat.choose m k : ℝ) =
        c S * ((Nat.choose k j : ℝ) / (Nat.choose m j : ℝ)) := by
      intro S hS
      have hScard : S.card = j := (Finset.mem_powersetCard.mp hS).2
      rw [hScard, mul_div_assoc, hratio]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    dsimp only [a]
    ring
  · -- If `j > m`, `powersetCard j univ = ∅` and `Nat.choose k j = 0` since `k ≤ m < j`.
    have hemp : Finset.powersetCard j (Finset.univ : Finset (Fin m)) = ∅ := by
      rw [Finset.powersetCard_eq_empty]
      simp; omega
    have hkj : Nat.choose k j = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hemp, hkj]

/-- **Univariate Polynomial Symmetrisation Theorem**:
For any Boolean function `f : BooleanFun m` of degree `≤ d`, there exists a univariate
real polynomial `q : ℝ[X]` of degree `≤ d` such that `q.eval (k : ℝ) = layerAvg f k`
for all `k ≤ m`. -/
theorem symmetrisation_polynomial {m d : ℕ} (f : BooleanFun m) (hf : polyDegree f ≤ d) :
    ∃ q : ℝ[X], q.natDegree ≤ d ∧
      ∀ k ≤ m, q.eval (k : ℝ) = layerAvg (fun x => boolToReal (f x)) k := by
  have hrep : ∀ x : Fin m → Bool,
      ∑ S ∈ (supportOf x).powerset, (mobiusCoeff f S : ℝ) = boolToReal (f x) := by
    intro x
    have h := representsPoly_mobius f x
    change MvPolynomial.eval (fun i => boolToReal (x i))
      (multilinearPoly (fun S => (mobiusCoeff f S : ℝ))) = boolToReal (f x) at h
    rwa [eval_multilinearPoly] at h
  have hdeg : ∀ S : Finset (Fin m), d < S.card → (mobiusCoeff f S : ℝ) = 0 := by
    intro S hS
    have h0 := mobiusCoeff_eq_zero_of_polyDegree_lt (lt_of_le_of_lt hf hS)
    simp [h0]
  obtain ⟨a, ha⟩ := layerAvg_eq_binomial_sum (fun x => boolToReal (f x))
    (fun S => (mobiusCoeff f S : ℝ)) hrep hdeg
  let q : ℝ[X] := ∑ j ∈ Finset.range (d + 1),
    Polynomial.C (a j / (Nat.factorial j : ℝ)) * descPochhammer ℝ j
  refine ⟨q, ?_, ?_⟩
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro r hr
    simp only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
    apply Finset.sum_eq_zero
    intro j hj
    have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hdegj : (descPochhammer ℝ j).natDegree < r := by
      rw [descPochhammer_natDegree]; omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdegj, mul_zero]
  · intro k hk
    rw [ha k hk]
    simp only [q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    apply Finset.sum_congr rfl
    intro j _
    rw [descPochhammer_eval_eq_descFactorial]
    have hfact : (Nat.factorial j : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hchoose : (Nat.descFactorial k j : ℝ) = (Nat.choose k j : ℝ) * (Nat.factorial j : ℝ) := by
      exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose k j).trans (mul_comm _ _)
    rw [hchoose]
    field_simp [hfact]

/-- **Exact Linear Identity Principle (Orthogonality to Binomial Basis)**:
If `g : {0, 1}^m → ℝ` has multilinear degree `≤ d` and `y : Fin (m + 1) → ℤ` satisfies
`∑ k : Fin (m + 1), y k * (Nat.choose k.1 j.1 : ℤ) = 0` for every `j : Fin (d + 1)`,
then `∑ k : Fin (m + 1), (y k : ℝ) * layerAvg g k.1 = 0`. -/
theorem symmetrisation_linear_identity {m d : ℕ} (g : (Fin m → Bool) → ℝ)
    (c : Finset (Fin m) → ℝ)
    (hrep : ∀ x : Fin m → Bool, ∑ S ∈ (supportOf x).powerset, c S = g x)
    (hdeg : ∀ S : Finset (Fin m), d < S.card → c S = 0)
    (y : Fin (m + 1) → ℤ)
    (horth : ∀ j : Fin (d + 1), ∑ k : Fin (m + 1), y k * (Nat.choose k.1 j.1 : ℤ) = 0) :
    ∑ k : Fin (m + 1), (y k : ℝ) * layerAvg g k.1 = 0 := by
  obtain ⟨a, ha⟩ := layerAvg_eq_binomial_sum g c hrep hdeg
  calc ∑ k : Fin (m + 1), (y k : ℝ) * layerAvg g k.1
      = ∑ k : Fin (m + 1), (y k : ℝ) *
          ∑ j ∈ Finset.range (d + 1), a j * (Nat.choose k.1 j : ℝ) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [ha k.1 (Nat.lt_succ_iff.mp k.2)]
    _ = ∑ k : Fin (m + 1), ∑ j ∈ Finset.range (d + 1),
          a j * ((y k : ℝ) * (Nat.choose k.1 j : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = ∑ j ∈ Finset.range (d + 1),
          a j * ∑ k : Fin (m + 1), (y k : ℝ) * (Nat.choose k.1 j : ℝ) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.mul_sum]
    _ = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hjd : j < d + 1 := Finset.mem_range.mp hj
        have h0 := horth ⟨j, hjd⟩
        have h0R : ∑ k : Fin (m + 1), (y k : ℝ) * (Nat.choose k.1 j : ℝ) = 0 := by
          exact_mod_cast h0
        rw [h0R, mul_zero]

/-- Specialization of `symmetrisation_linear_identity` to Boolean functions `f : BooleanFun m`. -/
theorem bool_symmetrisation_linear_identity {m d : ℕ} (f : BooleanFun m)
    (hf : polyDegree f ≤ d)
    (y : Fin (m + 1) → ℤ)
    (horth : ∀ j : Fin (d + 1), ∑ k : Fin (m + 1), y k * (Nat.choose k.1 j.1 : ℤ) = 0) :
    ∑ k : Fin (m + 1), (y k : ℝ) * layerAvg (fun x => boolToReal (f x)) k.1 = 0 := by
  refine symmetrisation_linear_identity (fun x => boolToReal (f x))
    (fun S => (mobiusCoeff f S : ℝ)) ?_ ?_ y horth
  · intro x
    have h := representsPoly_mobius f x
    change MvPolynomial.eval (fun i => boolToReal (x i))
      (multilinearPoly (fun S => (mobiusCoeff f S : ℝ))) = boolToReal (f x) at h
    rwa [eval_multilinearPoly] at h
  · intro S hS
    have h0 := mobiusCoeff_eq_zero_of_polyDegree_lt (lt_of_le_of_lt hf hS)
    simp [h0]

/-- **Exact Integer Farkas LP Certificate Checker**:
Checks in decidable integer arithmetic that `y : Fin (n + 1) → ℤ` is a valid Wellens
Farkas infeasibility certificate for `(n, d)`:
1. `∑_{k=0}^n y_k * C(k, j) = 0` for all `0 ≤ j ≤ d`, and
2. `0 < y 1 + ∑_{k ≥ 2} min (y k) 0`. -/
def checkWellensFarkas (n d : ℕ) (hn : 1 ≤ n) (y : Fin (n + 1) → ℤ) : Bool :=
  let orth := (List.finRange (d + 1)).all fun j =>
    (∑ k : Fin (n + 1), y k * (Nat.choose k.1 j.1 : ℤ)) == 0
  let margin : ℤ := y ⟨1, by omega⟩ +
    ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 1) => 2 ≤ k.1), min (y k) 0
  orth && decide (0 < margin)

/-- **Soundness of the Wellens Farkas Certificate Engine**:
If `checkWellensFarkas n d hn y = true`, then NO normalized `n`-bit Boolean function
of degree `≤ d` exists, and consequently EVERY Boolean function (on ANY number of bits!)
of degree `≤ d` has `maxSensitivity f < n`. -/
theorem maxSensitivity_lt_of_wellens_farkas {n d : ℕ} (hn : 1 ≤ n) (y : Fin (n + 1) → ℤ)
    (hcert : checkWellensFarkas n d hn y = true) :
    ∀ (m : ℕ) (f : BooleanFun m), polyDegree f ≤ d → maxSensitivity f < n := by
  simp only [checkWellensFarkas, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const, beq_iff_eq, decide_eq_true_eq] at hcert
  obtain ⟨horth, hmargin⟩ := hcert
  apply maxSensitivity_lt_of_no_normalized
  rintro ⟨g, hgdeg, hg0, hg1⟩
  have hsum := bool_symmetrisation_linear_identity g hgdeg y horth
  let p : Fin (n + 1) → ℝ := fun k => layerAvg (fun x => boolToReal (g x)) k.1
  have hp0 : p ⟨0, Nat.zero_lt_succ n⟩ = 0 := layerAvg_bool_zero hg0
  have hp1 : p ⟨1, by omega⟩ = 1 := layerAvg_bool_one hn hg1
  have hge : ∀ k : Fin (n + 1), 2 ≤ k.1 → ((min (y k) 0 : ℤ) : ℝ) ≤ (y k : ℝ) * p k := by
    intro k _
    have h0le : 0 ≤ p k := layerAvg_bool_nonneg g k.1
    have hle1 : p k ≤ 1 := layerAvg_bool_le_one g k.1 (Nat.lt_succ_iff.mp k.2)
    by_cases hy : y k ≤ 0
    · have hmin : min (y k) 0 = y k := min_eq_left hy
      rw [hmin]
      have hyR : (y k : ℝ) ≤ 0 := by exact_mod_cast hy
      nlinarith
    · have hpos : 0 ≤ y k := le_of_not_ge hy
      have hmin : min (y k) 0 = 0 := min_eq_right hpos
      rw [hmin, Int.cast_zero]
      have hyR : (0 : ℝ) ≤ (y k : ℝ) := by exact_mod_cast hpos
      exact mul_nonneg hyR h0le
  -- Split `Fin (n + 1)` into `0`, `1`, and `{k | 2 ≤ k.1}`.
  have hsplit : ∑ k : Fin (n + 1), (y k : ℝ) * p k =
      (y ⟨0, Nat.zero_lt_succ n⟩ : ℝ) * p ⟨0, Nat.zero_lt_succ n⟩ +
      (y ⟨1, by omega⟩ : ℝ) * p ⟨1, by omega⟩ +
      ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 1) => 2 ≤ k.1), (y k : ℝ) * p k := by
    let k0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    let k1 : Fin (n + 1) := ⟨1, by omega⟩
    have hk01 : k0 ≠ k1 := by
      intro h
      have hv : k0.1 = k1.1 := congrArg Fin.val h
      dsimp only [k0, k1] at hv
      omega
    have huniv : (Finset.univ : Finset (Fin (n + 1))) =
        insert k0 (insert k1 (Finset.univ.filter (fun k : Fin (n + 1) => 2 ≤ k.1))) := by
      ext k
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and, true_iff]
      by_cases h0k : k.1 = 0
      · left; exact Fin.ext h0k
      · by_cases h1k : k.1 = 1
        · right; left; exact Fin.ext h1k
        · right; right; omega
    have hnot0 : k0 ∉ insert k1 (Finset.univ.filter (fun k : Fin (n + 1) => 2 ≤ k.1)) := by
      simp [k0, k1]
    have hnot1 : k1 ∉ Finset.univ.filter (fun k : Fin (n + 1) => 2 ≤ k.1) := by
      simp [k1]
    conv_lhs => rw [huniv]
    rw [Finset.sum_insert hnot0, Finset.sum_insert hnot1]
    ring
  change ∑ k : Fin (n + 1), (y k : ℝ) * p k = 0 at hsum
  rw [hsplit, hp0, hp1, mul_zero, zero_add, mul_one] at hsum
  have hbound : (y ⟨1, by omega⟩ : ℝ) +
      ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 1) => 2 ≤ k.1), ((min (y k) 0 : ℤ) : ℝ) ≤
      (y ⟨1, by omega⟩ : ℝ) +
      ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 1) => 2 ≤ k.1), (y k : ℝ) * p k := by
    gcongr with k hk
    exact hge k (Finset.mem_filter.mp hk).2
  have hmarginR : (0 : ℝ) < (y ⟨1, by omega⟩ : ℝ) +
      ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 1) => 2 ≤ k.1), ((min (y k) 0 : ℤ) : ℝ) := by
    exact_mod_cast hmargin
  linarith

/-! ## Concrete Wellens LP Upper Bounds via Exact Integer Farkas Certificates -/

/-- Sharp upper bound for degree 2: `deg(f) ≤ 2 → s(f) ≤ 3` (impossibility of `(n = 4, d = 2)`). -/
theorem maxSensitivity_le_three_of_deg_le_two_proof :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 2 → maxSensitivity f ≤ 3 := by
  intro n f hf
  have h := maxSensitivity_lt_of_wellens_farkas (n := 4) (d := 2) (by decide)
    ![-3, 8, -6, 0, 1] (by decide) n f hf
  omega

/-- Sharp upper bound for degree 3: `deg(f) ≤ 3 → s(f) ≤ 6` (impossibility of `(n = 7, d = 3)`). -/
theorem maxSensitivity_le_six_of_deg_le_three_proof :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 3 → maxSensitivity f ≤ 6 := by
  intro n f hf
  have h := maxSensitivity_lt_of_wellens_farkas (n := 7) (d := 3) (by decide)
    ![-12, 35, -28, 0, 0, 7, 0, -2] (by decide) n f hf
  omega

/-- Wellens LP bound for degree 4: `deg(f) ≤ 4 → s(f) ≤ 10` (impossibility of `(n = 11, d = 4)`). -/
theorem maxSensitivity_le_ten_of_deg_le_four_proof :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 4 → maxSensitivity f ≤ 10 := by
  intro n f hf
  have h := maxSensitivity_lt_of_wellens_farkas (n := 11) (d := 4) (by decide)
    ![-672, 2079, -1760, 0, 0, 462, 0, 0, 0, -165, 0, 56] (by decide) n f hf
  omega

/-- Wellens LP bound for degree 5: `deg(f) ≤ 5 → s(f) ≤ 15` (impossibility of `(n = 16, d = 5)`). -/
theorem maxSensitivity_le_fifteen_of_deg_le_five_proof :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 5 → maxSensitivity f ≤ 15 := by
  intro n f hf
  have h := maxSensitivity_lt_of_wellens_farkas (n := 16) (d := 5) (by decide)
    ![-1170, 3584, -2925, 0, 0, 0, 819, 0, 0, 0, -455, 0, 0, 0, 225, 0, -78] (by decide) n f hf
  omega

/-- Wellens LP bound for degree 6: `deg(f) ≤ 6 → s(f) ≤ 21` (impossibility of `(n = 22, d = 6)`). -/
theorem maxSensitivity_le_twentyone_of_deg_le_six_proof :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 6 → maxSensitivity f ≤ 21 := by
  intro n f hf
  have h := maxSensitivity_lt_of_wellens_farkas (n := 22) (d := 6) (by decide)
    ![-89775, 278784, -229900, 0, 0, 0, 62073, 0, 0, 0, 0, -34048,
      0, 0, 0, 0, 20691, 0, 0, 0, -12100, 0, 4275] (by decide) n f hf
  omega

end DegreeSensitivity
