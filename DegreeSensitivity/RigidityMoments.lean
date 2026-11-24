module

public import DegreeSensitivity.TerwilligerCore

@[expose] public section

/-!
# Polymorphic Weight-3/4 Moment Identities & Link-Graph Rigidity Reduction

All lemmas in this module are polymorphic over arbitrary dimension `n : ℕ` (never unfolding
concrete `Finset.univ : Finset (Fin n → Bool)`), providing fast, reusable combinatorial machinery
shared by both:
- `B_5 ≤ 14` (`n = 15`, `m = 14`, `d0 = 8`, `r = 5`), and
- `B_6 ≤ 20` (`n = 21`, `m = 20`, `d0 = 12`, `r = 7`).

Specifically, we prove:
1. Exact constant-layer extraction (`eq_true_of_layerAvg_eq_one`, `eq_false_of_layerAvg_eq_zero`)
   and coordinate restriction (`restrictFalse`, `polyDegree_restrictFalse_le`).
2. `sum_coordDeg3_sq`: `∑ i, D^(3)(i)^2 = ∑_{t=0}^3 t * pairCount n 3 3 t * m(3, 3, t)`.
3. Pair-degree moments (`sum_pairDeg3`, `sum_pairDeg3_sq`) and quad-degree moments
   (`sum_quad_f`, `sum_quadDeg3`, `sum_quad_f_mul_quadDeg3`, `sum_quadDeg3_sq`).
4. `exists_reg_trifree_2k2free_of_rigidity`: rigid `d^(3)(P) = d0` and `t(Q) = 2 + 2 f(Q)`
   produce an `(m - 1 - d0)`-regular, triangle-free, induced-`2K₂`-free simple graph on `Fin m`.
-/

namespace DegreeSensitivity

open scoped BigOperators

/-! ### Part 1: Basic Membership & Constant-Layer Helpers -/

lemma mem_hammingLayer_iff {n k : ℕ} {x : Fin n → Bool} :
    x ∈ hammingLayer n k ↔ (supportOf x).card = k := by
  simp [hammingLayer]

lemma pairSet_eq_filter {n i j t : ℕ} :
    (hammingLayer n i ×ˢ hammingLayer n j).filter (fun p => (supportOf p.1 ∩ supportOf p.2).card = t) =
      pairSet n i j t := rfl

lemma mem_pairSet_iff {n i j t : ℕ} {p : (Fin n → Bool) × (Fin n → Bool)} :
    p ∈ pairSet n i j t ↔
      p.1 ∈ hammingLayer n i ∧ p.2 ∈ hammingLayer n j ∧ (supportOf p.1 ∩ supportOf p.2).card = t := by
  simp [pairSet, Finset.mem_filter, Finset.mem_product, and_assoc]

lemma card_four_finset {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset α).card = 4 := by
  simp [hab, hac, had, hbc, hbd, hcd]

lemma eq_true_of_layerAvg_eq_one {n k : ℕ} (f : BooleanFun n) (hk : k ≤ n)
    (h1 : layerAvg (fun x => boolToReal (f x)) k = 1) :
    ∀ x ∈ hammingLayer n k, f x = true := by
  have hpos : (0 : ℝ) < (Nat.choose n k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have hsum : ∑ x ∈ hammingLayer n k, boolToReal (f x) = ((hammingLayer n k).card : ℝ) := by
    rw [card_hammingLayer]
    have := congrArg (fun r => r * (Nat.choose n k : ℝ)) h1
    simp only [layerAvg, realLayerSum, one_mul] at this
    rwa [div_mul_cancel₀ _ hpos.ne'] at this
  have hdiff : ∑ x ∈ hammingLayer n k, (1 - boolToReal (f x)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hsum, sub_self]
  have hnn : ∀ x ∈ hammingLayer n k, 0 ≤ 1 - boolToReal (f x) := by
    intro x _; cases f x <;> norm_num [boolToReal]
  intro x hx
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hdiff x hx
  cases hfx : f x
  · simp [boolToReal, hfx] at h0
  · rfl

lemma eq_false_of_layerAvg_eq_zero {n k : ℕ} (f : BooleanFun n) (hk : k ≤ n)
    (h0 : layerAvg (fun x => boolToReal (f x)) k = 0) :
    ∀ x ∈ hammingLayer n k, f x = false := by
  have hpos : (0 : ℝ) < (Nat.choose n k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have hsum : ∑ x ∈ hammingLayer n k, boolToReal (f x) = 0 := by
    have := congrArg (fun r => r * (Nat.choose n k : ℝ)) h0
    simp only [layerAvg, realLayerSum, zero_mul] at this
    rwa [div_mul_cancel₀ _ hpos.ne'] at this
  have hnn : ∀ x ∈ hammingLayer n k, 0 ≤ boolToReal (f x) := by
    intro x _; cases f x <;> norm_num [boolToReal]
  intro x hx
  have hx0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum x hx
  cases hfx : f x
  · rfl
  · simp [boolToReal, hfx] at hx0

/-! ### Part 2: Coordinate Restriction (`x_i = false`) -/

/-- Restrict `f : BooleanFun (n + 1)` by fixing coordinate `i` to `false`. -/
def restrictFalse {n : ℕ} (f : BooleanFun (n + 1)) (i : Fin (n + 1)) : BooleanFun n :=
  fun y => f (i.insertNth false y)

lemma insertNth_false_zeroVec {n : ℕ} (i : Fin (n + 1)) :
    i.insertNth false (zeroVec n) = zeroVec (n + 1) := by
  funext k
  refine Fin.succAboveCases i ?_ ?_ k
  · simp [zeroVec]
  · intro j; simp [zeroVec]

lemma insertNth_false_basisVec {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    i.insertNth false (basisVec j) = basisVec (i.succAbove j) := by
  funext k
  refine Fin.succAboveCases i ?_ ?_ k
  · simp [basisVec, zeroVec, (Fin.succAbove_ne i j).symm]
  · intro m
    simp only [Fin.insertNth_apply_succAbove, basisVec_apply]
    by_cases hmj : m = j
    · subst hmj; simp
    · have hne : i.succAbove m ≠ i.succAbove j := fun h => hmj (Fin.succAbove_right_injective h)
      simp [hmj, hne]

lemma supportOf_insertNth_false {n : ℕ} (i : Fin (n + 1)) (y : Fin n → Bool) :
    supportOf (i.insertNth false y) = (supportOf y).map (Fin.succAboveEmb i) := by
  ext k
  simp only [mem_supportOf, Finset.mem_map, Fin.succAboveEmb_apply]
  refine Fin.succAboveCases i ?_ ?_ k
  · simp [Fin.succAbove_ne]
  · intro j
    simp only [Fin.insertNth_apply_succAbove]
    constructor
    · intro h; exact ⟨j, h, rfl⟩
    · rintro ⟨a, ha, hEq⟩
      rw [← Fin.succAbove_right_injective hEq]; exact ha

lemma card_supportOf_insertNth_false {n : ℕ} (i : Fin (n + 1)) (y : Fin n → Bool) :
    (supportOf (i.insertNth false y)).card = (supportOf y).card := by
  rw [supportOf_insertNth_false, Finset.card_map]

lemma polyDegree_restrictFalse_le {n : ℕ} (f : BooleanFun (n + 1)) (i : Fin (n + 1)) :
    polyDegree (restrictFalse f i) ≤ polyDegree f := by
  rw [polyDegree_le_iff]
  obtain ⟨P, hPrep, hPdeg⟩ := polyDegree_le_iff.mp (le_refl (polyDegree f))
  let g : Fin (n + 1) → MvPolynomial (Fin n) ℝ :=
    i.insertNth (0 : MvPolynomial (Fin n) ℝ) MvPolynomial.X
  refine ⟨MvPolynomial.aeval g P, ?_, ?_⟩
  · intro y
    change MvPolynomial.eval (fun j => boolToReal (y j)) (MvPolynomial.aeval g P) =
      boolToReal (f (i.insertNth false y))
    rw [eval_aeval_eq]
    have hvar : (fun k => MvPolynomial.eval (fun j => boolToReal (y j)) (g k)) =
        (fun k => boolToReal ((i.insertNth false y : Fin (n + 1) → Bool) k)) := by
      funext k
      refine Fin.succAboveCases i ?_ ?_ k
      · simp [g, boolToReal]
      · intro j; simp [g]
    rw [hvar]
    exact hPrep (i.insertNth false y)
  · have hg_deg : ∀ k : Fin (n + 1), (g k).totalDegree ≤ 1 := by
      intro k
      refine Fin.succAboveCases i ?_ ?_ k
      · simp [g]
      · intro j; simp [g, MvPolynomial.totalDegree_X]
    have h := totalDegree_aeval_le_mul g P 1 hg_deg
    rw [one_mul] at h
    exact h.trans hPdeg

lemma sum_layer_filter_false_eq_restrict {n k : ℕ} (f : BooleanFun (n + 1)) (i : Fin (n + 1)) :
    ∑ x ∈ (hammingLayer (n + 1) k).filter (fun x => x i = false), boolToReal (f x) =
      realLayerSum (fun y => boolToReal (restrictFalse f i y)) k := by
  unfold realLayerSum restrictFalse
  symm
  refine Finset.sum_nbij (fun y => i.insertNth false y) ?_ ?_ ?_ ?_
  · intro y hy
    have hcard : (supportOf y).card = k := mem_hammingLayer_iff.mp hy
    rw [Finset.mem_filter, mem_hammingLayer_iff]
    exact ⟨by rw [card_supportOf_insertNth_false, hcard], by simp⟩
  · intro y₁ _ y₂ _ hEq
    funext j
    have := congrFun hEq (i.succAbove j)
    simpa using this
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, mem_hammingLayer_iff] at hx
    obtain ⟨hxk, hxi⟩ := hx
    refine ⟨i.removeNth x, ?_, ?_⟩
    · rw [Finset.mem_coe, mem_hammingLayer_iff]
      have hrec : i.insertNth false (i.removeNth x) = x := by
        funext j
        refine Fin.succAboveCases i ?_ ?_ j
        · simp [hxi]
        · intro m; simp [Fin.removeNth]
      rw [← card_supportOf_insertNth_false i, hrec, hxk]
    · funext j
      refine Fin.succAboveCases i ?_ ?_ j
      · simp [hxi]
      · intro m; simp [Fin.removeNth]
  · intro y _; rfl

/-! ### Part 3: Polymorphic Weight-3/4 Degree Definitions & Moment Identities -/

/-- Number of weight-3 ones containing coordinate `i`. -/
noncomputable def coordDeg3 {n : ℕ} (f : BooleanFun n) (i : Fin n) : ℝ :=
  ∑ x ∈ (hammingLayer n 3).filter (fun x => x i = true), boolToReal (f x)

/-- Number of weight-3 ones containing a 2-subset `P`. -/
noncomputable def pairDeg3 {n : ℕ} (f : BooleanFun n) (P : Finset (Fin n)) : ℝ :=
  ∑ x ∈ (hammingLayer n 3).filter (fun x => P ⊆ supportOf x), boolToReal (f x)

/-- Number of weight-3 ones contained in a 4-subset `Q`. -/
noncomputable def quadDeg3 {n : ℕ} (f : BooleanFun n) (Q : Finset (Fin n)) : ℝ :=
  ∑ x ∈ (hammingLayer n 3).filter (fun x => supportOf x ⊆ Q), boolToReal (f x)

lemma coordDeg3_add_restrictFalse {n : ℕ} (f : BooleanFun (n + 1)) (i : Fin (n + 1)) :
    coordDeg3 f i + realLayerSum (fun y => boolToReal (restrictFalse f i y)) 3 =
      realLayerSum (fun x => boolToReal (f x)) 3 := by
  rw [← sum_layer_filter_false_eq_restrict f i]
  dsimp only [coordDeg3, realLayerSum]
  have hfilt := Finset.sum_filter_add_sum_filter_not (hammingLayer (n + 1) 3)
    (fun x => x i = true) (fun x => boolToReal (f x))
  have hnot : (hammingLayer (n + 1) 3).filter (fun x => ¬ x i = true) =
      (hammingLayer (n + 1) 3).filter (fun x => x i = false) := by
    apply Finset.filter_congr; intro x _; cases x i <;> simp
  rw [hnot] at hfilt
  exact hfilt

theorem sum_coordDeg3_sq {n : ℕ} (hn : 6 ≤ n) (f : BooleanFun n) :
    ∑ i : Fin n, (coordDeg3 f i) ^ 2 =
      ∑ t ∈ Finset.range 4, (t : ℝ) * ((pairCount n 3 3 t : ℝ) * pairCorr f 3 3 t) := by
  have hrhs : ∑ i : Fin n, (coordDeg3 f i) ^ 2 =
      ∑ p ∈ hammingLayer n 3 ×ˢ hammingLayer n 3,
        ((supportOf p.1 ∩ supportOf p.2).card : ℝ) * (boolToReal (f p.1) * boolToReal (f p.2)) := by
    have hsq : ∀ i : Fin n, (coordDeg3 f i) ^ 2 =
        ∑ p ∈ hammingLayer n 3 ×ˢ hammingLayer n 3,
          (if i ∈ supportOf p.1 ∩ supportOf p.2 then (1 : ℝ) else 0) *
            (boolToReal (f p.1) * boolToReal (f p.2)) := by
      intro i
      dsimp only [coordDeg3]
      rw [sq, Finset.sum_filter, Finset.sum_mul_sum, ← Finset.sum_product']
      apply Finset.sum_congr rfl
      rintro ⟨x, y⟩ _
      simp only [Finset.mem_inter, mem_supportOf]
      by_cases hx : x i = true <;> by_cases hy : y i = true <;> simp [hx, hy]
    calc ∑ i : Fin n, (coordDeg3 f i) ^ 2
        = ∑ i : Fin n, ∑ p ∈ hammingLayer n 3 ×ˢ hammingLayer n 3,
            (if i ∈ supportOf p.1 ∩ supportOf p.2 then (1 : ℝ) else 0) *
              (boolToReal (f p.1) * boolToReal (f p.2)) :=
          Finset.sum_congr rfl (fun i _ => hsq i)
      _ = ∑ p ∈ hammingLayer n 3 ×ˢ hammingLayer n 3,
            ∑ i : Fin n,
              (if i ∈ supportOf p.1 ∩ supportOf p.2 then (1 : ℝ) else 0) *
                (boolToReal (f p.1) * boolToReal (f p.2)) := Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl; intro p _
          rw [← Finset.sum_mul]
          have hcard : ∑ i : Fin n, (if i ∈ supportOf p.1 ∩ supportOf p.2 then (1 : ℝ) else 0) =
              ((supportOf p.1 ∩ supportOf p.2).card : ℝ) := by
            rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
          rw [hcard]
  rw [hrhs]
  have hmaps : ∀ p ∈ hammingLayer n 3 ×ˢ hammingLayer n 3,
      (supportOf p.1 ∩ supportOf p.2).card ∈ Finset.range 4 := by
    intro p hp
    have h1 : (supportOf p.1).card = 3 := mem_hammingLayer_iff.mp (Finset.mem_product.mp hp).1
    have hle : (supportOf p.1 ∩ supportOf p.2).card ≤ 3 :=
      (Finset.card_le_card Finset.inter_subset_left).trans h1.le
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro t ht
  have ht3 : t ≤ 3 := by rw [Finset.mem_range] at ht; omega
  have hvalid : ValidTriple n 3 3 t := ⟨by omega, by omega, ht3, ht3, by omega⟩
  have hpc : (pairCount n 3 3 t : ℝ) ≠ 0 := by exact_mod_cast (pairCount_pos hvalid).ne'
  have hmul : (pairCount n 3 3 t : ℝ) * pairCorr f 3 3 t =
      ∑ p ∈ pairSet n 3 3 t, boolToReal (f p.1) * boolToReal (f p.2) := by
    unfold pairCorr; field_simp [hpc]
  rw [pairSet_eq_filter, hmul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hcard : (supportOf p.1 ∩ supportOf p.2).card = t := (mem_pairSet_iff.mp hp).2.2
  rw [hcard]

theorem sum_pairDeg3 {n : ℕ} (f : BooleanFun n) :
    ∑ P ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)), pairDeg3 f P =
      3 * realLayerSum (fun x => boolToReal (f x)) 3 := by
  set Pairs := Finset.powersetCard 2 (Finset.univ : Finset (Fin n))
  calc ∑ P ∈ Pairs, pairDeg3 f P
      = ∑ P ∈ Pairs, ∑ x ∈ hammingLayer n 3,
          if P ⊆ supportOf x then boolToReal (f x) else 0 := by
        apply Finset.sum_congr rfl; intro P _; simp [pairDeg3, Finset.sum_filter]
    _ = ∑ x ∈ hammingLayer n 3, ∑ P ∈ Pairs,
          if P ⊆ supportOf x then boolToReal (f x) else 0 := Finset.sum_comm
    _ = ∑ x ∈ hammingLayer n 3,
          ((Finset.powersetCard 2 (supportOf x)).card : ℝ) * boolToReal (f x) := by
        apply Finset.sum_congr rfl; intro x _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have hfilt : Pairs.filter (fun P => P ⊆ supportOf x) =
            Finset.powersetCard 2 (supportOf x) := by
          ext P; simp [Pairs, Finset.mem_powersetCard, and_comm]
        rw [hfilt]
    _ = 3 * realLayerSum (fun x => boolToReal (f x)) 3 := by
        rw [realLayerSum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro x hx
        have hx3 : (supportOf x).card = 3 := mem_hammingLayer_iff.mp hx
        rw [Finset.card_powersetCard, hx3]; norm_num

theorem sum_pairDeg3_sq {n : ℕ} (hn : 6 ≤ n) (f : BooleanFun n) :
    ∑ P ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)), (pairDeg3 f P) ^ 2 =
      (pairCount n 3 3 2 : ℝ) * pairCorr f 3 3 2 +
        3 * realLayerSum (fun x => boolToReal (f x)) 3 := by
  set Pairs := Finset.powersetCard 2 (Finset.univ : Finset (Fin n))
  have h1 : ∑ P ∈ Pairs, (pairDeg3 f P) ^ 2 =
      ∑ p ∈ hammingLayer n 3 ×ˢ hammingLayer n 3,
        ((Finset.powersetCard 2 (supportOf p.1 ∩ supportOf p.2)).card : ℝ) *
          (boolToReal (f p.1) * boolToReal (f p.2)) := by
    calc ∑ P ∈ Pairs, (pairDeg3 f P) ^ 2
        = ∑ P ∈ Pairs, ∑ p ∈ hammingLayer n 3 ×ˢ hammingLayer n 3,
            if P ⊆ supportOf p.1 ∩ supportOf p.2 then boolToReal (f p.1) * boolToReal (f p.2) else 0 := by
          apply Finset.sum_congr rfl; intro P _
          dsimp only [pairDeg3]
          rw [sq, Finset.sum_filter, Finset.sum_mul_sum, ← Finset.sum_product']
          apply Finset.sum_congr rfl; rintro ⟨x, y⟩ _
          by_cases h1 : P ⊆ supportOf x <;> by_cases h2 : P ⊆ supportOf y <;>
            simp [Finset.subset_inter_iff, h1, h2]
      _ = ∑ p ∈ hammingLayer n 3 ×ˢ hammingLayer n 3, ∑ P ∈ Pairs,
            if P ⊆ supportOf p.1 ∩ supportOf p.2 then boolToReal (f p.1) * boolToReal (f p.2) else 0 :=
          Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl; intro p _
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have hfilt : Pairs.filter (fun P => P ⊆ supportOf p.1 ∩ supportOf p.2) =
              Finset.powersetCard 2 (supportOf p.1 ∩ supportOf p.2) := by
            ext P; simp [Pairs, Finset.mem_powersetCard, and_comm]
          rw [hfilt]
  rw [h1]
  have hmaps : ∀ p ∈ hammingLayer n 3 ×ˢ hammingLayer n 3,
      (supportOf p.1 ∩ supportOf p.2).card ∈ Finset.range 4 := by
    intro p hp
    have h3 : (supportOf p.1).card = 3 := mem_hammingLayer_iff.mp (Finset.mem_product.mp hp).1
    have hle : (supportOf p.1 ∩ supportOf p.2).card ≤ 3 :=
      (Finset.card_le_card Finset.inter_subset_left).trans h3.le
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hterm : ∀ t ∈ Finset.range 4,
      ∑ p ∈ (hammingLayer n 3 ×ˢ hammingLayer n 3).filter
          (fun p => (supportOf p.1 ∩ supportOf p.2).card = t),
        ((Finset.powersetCard 2 (supportOf p.1 ∩ supportOf p.2)).card : ℝ) *
          (boolToReal (f p.1) * boolToReal (f p.2)) =
      (Nat.choose t 2 : ℝ) * ((pairCount n 3 3 t : ℝ) * pairCorr f 3 3 t) := by
    intro t ht
    have ht3 : t ≤ 3 := by rw [Finset.mem_range] at ht; omega
    have hvalid : ValidTriple n 3 3 t := ⟨by omega, by omega, ht3, ht3, by omega⟩
    have hpc : (pairCount n 3 3 t : ℝ) ≠ 0 := by exact_mod_cast (pairCount_pos hvalid).ne'
    have hmul : (pairCount n 3 3 t : ℝ) * pairCorr f 3 3 t =
        ∑ p ∈ pairSet n 3 3 t, boolToReal (f p.1) * boolToReal (f p.2) := by
      unfold pairCorr; field_simp [hpc]
    rw [pairSet_eq_filter, hmul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p hp
    have hc : (supportOf p.1 ∩ supportOf p.2).card = t := (mem_pairSet_iff.mp hp).2.2
    rw [Finset.card_powersetCard, hc]
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  have hdiag : (pairCount n 3 3 3 : ℝ) * pairCorr f 3 3 3 =
      realLayerSum (fun x => boolToReal (f x)) 3 := by
    rw [pairCorr_diag f (by omega), layerAvg, pairCount]
    have hc3 : (Nat.choose n 3 : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega : 3 ≤ n)).ne'
    simp only [Nat.choose_self, Nat.sub_self, Nat.choose_zero_right, mul_one]
    field_simp [hc3]
  have h2 : Nat.choose 2 2 = 1 := by decide
  have h3 : Nat.choose 3 2 = 3 := by decide
  have h0 : Nat.choose 0 2 = 0 := by decide
  have h1c : Nat.choose 1 2 = 0 := by decide
  rw [h0, h1c, h2, h3, hdiag]
  push_cast; ring

theorem sum_quad_f {n : ℕ} (f : BooleanFun n) :
    ∑ Q ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin n)), boolToReal (f (indicator Q)) =
      realLayerSum (fun x => boolToReal (f x)) 4 := by
  unfold realLayerSum
  apply Finset.sum_nbij indicator
  · intro Q hQ
    rw [mem_hammingLayer_iff, supportOf_indicator]
    exact (Finset.mem_powersetCard.mp hQ).2
  · intro Q₁ _ Q₂ _ hEq
    have := congrArg supportOf hEq; simpa [supportOf_indicator] using this
  · intro y hy
    refine ⟨supportOf y, ?_, indicator_supportOf y⟩
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, mem_hammingLayer_iff.mp hy⟩
  · intro _ _; rfl

private lemma card_quads_superset_three {n : ℕ} (U : Finset (Fin n)) (hU3 : U.card = 3) :
    ((Finset.powersetCard 4 (Finset.univ : Finset (Fin n))).filter (fun Q => U ⊆ Q)).card =
      n - 3 := by
  set Quads := Finset.powersetCard 4 (Finset.univ : Finset (Fin n))
  have hbij : (Quads.filter (fun Q => U ⊆ Q)).card = Uᶜ.card := by
    symm
    apply Finset.card_bij (fun a _ => insert a U)
    · intro a ha
      have hnot : a ∉ U := Finset.mem_compl.mp ha
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ _, by rw [Finset.card_insert_of_notMem hnot, hU3]⟩,
        Finset.subset_insert a U⟩
    · intro a₁ ha₁ a₂ ha₂ hEq
      have hnot : a₁ ∉ U := Finset.mem_compl.mp ha₁
      have hmem : a₁ ∈ insert a₂ U := by rw [← hEq]; exact Finset.mem_insert_self a₁ U
      exact (Finset.mem_insert.mp hmem).resolve_right hnot
    · intro Q hQ
      obtain ⟨hQ4, hsub⟩ := Finset.mem_filter.mp hQ
      have hcardQ4 : Q.card = 4 := (Finset.mem_powersetCard.mp hQ4).2
      have hsdiff : (Q \ U).card = 1 := by rw [Finset.card_sdiff_of_subset hsub, hcardQ4, hU3]
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hsdiff
      have ha_mem : a ∈ Q \ U := by rw [ha]; exact Finset.mem_singleton_self a
      obtain ⟨haQ, ha_not⟩ := Finset.mem_sdiff.mp ha_mem
      refine ⟨a, Finset.mem_compl.mpr ha_not, ?_⟩
      ext k; simp only [Finset.mem_insert]
      constructor
      · rintro (rfl | hk); exact haQ; exact hsub hk
      · intro hkQ
        by_cases hkU : k ∈ U
        · exact Or.inr hkU
        · left
          have : k ∈ Q \ U := Finset.mem_sdiff.mpr ⟨hkQ, hkU⟩
          rw [ha, Finset.mem_singleton] at this; exact this
  rw [hbij, Finset.card_compl, Fintype.card_fin, hU3]

theorem sum_quadDeg3 {n : ℕ} (f : BooleanFun n) :
    ∑ Q ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin n)), quadDeg3 f Q =
      ((n - 3 : ℕ) : ℝ) * realLayerSum (fun x => boolToReal (f x)) 3 := by
  set Quads := Finset.powersetCard 4 (Finset.univ : Finset (Fin n))
  calc ∑ Q ∈ Quads, quadDeg3 f Q
      = ∑ Q ∈ Quads, ∑ x ∈ hammingLayer n 3,
          if supportOf x ⊆ Q then boolToReal (f x) else 0 := by
        apply Finset.sum_congr rfl; intro Q _; simp [quadDeg3, Finset.sum_filter]
    _ = ∑ x ∈ hammingLayer n 3, ∑ Q ∈ Quads,
          if supportOf x ⊆ Q then boolToReal (f x) else 0 := Finset.sum_comm
    _ = ∑ x ∈ hammingLayer n 3,
          ((Quads.filter (fun Q => supportOf x ⊆ Q)).card : ℝ) * boolToReal (f x) := by
        apply Finset.sum_congr rfl; intro x _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ = ((n - 3 : ℕ) : ℝ) * realLayerSum (fun x => boolToReal (f x)) 3 := by
        rw [realLayerSum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro x hx
        rw [card_quads_superset_three (supportOf x) (mem_hammingLayer_iff.mp hx)]

theorem sum_quad_f_mul_quadDeg3 {n : ℕ} (hn : 4 ≤ n) (f : BooleanFun n) :
    ∑ Q ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin n)),
        boolToReal (f (indicator Q)) * quadDeg3 f Q =
      (pairCount n 3 4 3 : ℝ) * pairCorr f 3 4 3 := by
  set Quads := Finset.powersetCard 4 (Finset.univ : Finset (Fin n))
  have hvalid : ValidTriple n 3 4 3 := ⟨by omega, hn, le_refl 3, by omega, by omega⟩
  have hpc : (pairCount n 3 4 3 : ℝ) ≠ 0 := by exact_mod_cast (pairCount_pos hvalid).ne'
  have hmul : (pairCount n 3 4 3 : ℝ) * pairCorr f 3 4 3 =
      ∑ p ∈ pairSet n 3 4 3, boolToReal (f p.1) * boolToReal (f p.2) := by
    unfold pairCorr; field_simp [hpc]
  rw [hmul]
  calc ∑ Q ∈ Quads, boolToReal (f (indicator Q)) * quadDeg3 f Q
      = ∑ Q ∈ Quads, ∑ x ∈ (hammingLayer n 3).filter (fun x => supportOf x ⊆ Q),
          boolToReal (f x) * boolToReal (f (indicator Q)) := by
        apply Finset.sum_congr rfl; intro Q _
        rw [quadDeg3, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro x _; ring
    _ = ∑ p ∈ Quads.sigma (fun Q => (hammingLayer n 3).filter (fun x => supportOf x ⊆ Q)),
          boolToReal (f p.2) * boolToReal (f (indicator p.1)) :=
        (Finset.sum_sigma Quads (fun Q => (hammingLayer n 3).filter (fun x => supportOf x ⊆ Q))
          (fun p => boolToReal (f p.2) * boolToReal (f (indicator p.1)))).symm
    _ = ∑ p ∈ pairSet n 3 4 3, boolToReal (f p.1) * boolToReal (f p.2) := by
        apply Finset.sum_nbij (fun p => (p.2, indicator p.1))
        · rintro ⟨Q, x⟩ hp
          simp only [Finset.mem_sigma, Finset.mem_filter] at hp
          obtain ⟨hQ, hxL, hsub⟩ := hp
          rw [mem_pairSet_iff, mem_hammingLayer_iff, mem_hammingLayer_iff, supportOf_indicator]
          have hx3 : (supportOf x).card = 3 := mem_hammingLayer_iff.mp hxL
          have hQ4 : Q.card = 4 := (Finset.mem_powersetCard.mp hQ).2
          exact ⟨hx3, hQ4, by rw [Finset.inter_eq_left.mpr hsub, hx3]⟩
        · rintro ⟨Q₁, x₁⟩ _ ⟨Q₂, x₂⟩ _ hEq
          have hx : x₁ = x₂ := congrArg Prod.fst hEq
          have hQ : Q₁ = Q₂ := by
            have := congrArg (fun p => supportOf p.2) hEq
            simpa [supportOf_indicator] using this
          subst hx; subst hQ; rfl
        · rintro ⟨x, y⟩ hp
          rw [Finset.mem_coe, mem_pairSet_iff, mem_hammingLayer_iff, mem_hammingLayer_iff] at hp
          obtain ⟨hx3, hy4, hinter⟩ := hp
          dsimp only at hx3 hy4 hinter
          have hsub : supportOf x ⊆ supportOf y := by
            have heq : supportOf x ∩ supportOf y = supportOf x :=
              Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
            rw [← heq]; exact Finset.inter_subset_right
          refine ⟨⟨supportOf y, x⟩, ?_, by simp [indicator_supportOf]⟩
          simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Quads,
            Finset.mem_powersetCard, mem_hammingLayer_iff]
          exact ⟨⟨Finset.subset_univ _, hy4⟩, hx3, hsub⟩
        · intro _ _; rfl

theorem sum_quadDeg3_sq {n : ℕ} (hn : 6 ≤ n) (f : BooleanFun n) :
    ∑ Q ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin n)), (quadDeg3 f Q) ^ 2 =
      (pairCount n 3 3 2 : ℝ) * pairCorr f 3 3 2 +
        ((n - 3 : ℕ) : ℝ) * realLayerSum (fun x => boolToReal (f x)) 3 := by
  set Quads := Finset.powersetCard 4 (Finset.univ : Finset (Fin n))
  have h1 : ∑ Q ∈ Quads, (quadDeg3 f Q) ^ 2 =
      ∑ p ∈ hammingLayer n 3 ×ˢ hammingLayer n 3,
        ((Quads.filter (fun Q => supportOf p.1 ∪ supportOf p.2 ⊆ Q)).card : ℝ) *
          (boolToReal (f p.1) * boolToReal (f p.2)) := by
    calc ∑ Q ∈ Quads, (quadDeg3 f Q) ^ 2
        = ∑ Q ∈ Quads, ∑ p ∈ hammingLayer n 3 ×ˢ hammingLayer n 3,
            if supportOf p.1 ∪ supportOf p.2 ⊆ Q then boolToReal (f p.1) * boolToReal (f p.2) else 0 := by
          apply Finset.sum_congr rfl; intro Q _
          dsimp only [quadDeg3]
          rw [sq, Finset.sum_filter, Finset.sum_mul_sum, ← Finset.sum_product']
          apply Finset.sum_congr rfl; rintro ⟨x, y⟩ _
          by_cases h1 : supportOf x ⊆ Q <;> by_cases h2 : supportOf y ⊆ Q <;>
            simp [Finset.union_subset_iff, h1, h2]
      _ = ∑ p ∈ hammingLayer n 3 ×ˢ hammingLayer n 3, ∑ Q ∈ Quads,
            if supportOf p.1 ∪ supportOf p.2 ⊆ Q then boolToReal (f p.1) * boolToReal (f p.2) else 0 :=
          Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl; intro p _
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [h1]
  have hmaps : ∀ p ∈ hammingLayer n 3 ×ˢ hammingLayer n 3,
      (supportOf p.1 ∩ supportOf p.2).card ∈ Finset.range 4 := by
    intro p hp
    have h3 : (supportOf p.1).card = 3 := mem_hammingLayer_iff.mp (Finset.mem_product.mp hp).1
    have hle : (supportOf p.1 ∩ supportOf p.2).card ≤ 3 :=
      (Finset.card_le_card Finset.inter_subset_left).trans h3.le
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hcntU : ∀ (t : ℕ) (p : (Fin n → Bool) × (Fin n → Bool)),
      p ∈ pairSet n 3 3 t →
      (Quads.filter (fun Q => supportOf p.1 ∪ supportOf p.2 ⊆ Q)).card =
        if t = 3 then n - 3 else if t = 2 then 1 else 0 := by
    intro t p hp
    rw [mem_pairSet_iff, mem_hammingLayer_iff, mem_hammingLayer_iff] at hp
    obtain ⟨h1, h2, ht⟩ := hp
    set U := supportOf p.1 ∪ supportOf p.2
    have hUcard : U.card + t = 6 := by
      have hinc := Finset.card_union_add_card_inter (supportOf p.1) (supportOf p.2)
      change U.card + (supportOf p.1 ∩ supportOf p.2).card = _ at hinc
      omega
    by_cases ht3 : t = 3
    · subst ht3; simp only [↓reduceIte]
      exact card_quads_superset_three U (by omega)
    · by_cases ht2 : t = 2
      · subst ht2
        simp only [show (2 : ℕ) ≠ 3 by omega, ↓reduceIte]
        have hU4 : U.card = 4 := by omega
        have heq : Quads.filter (fun Q => U ⊆ Q) = {U} := by
          ext Q
          simp only [Finset.mem_filter, Finset.mem_singleton, Quads, Finset.mem_powersetCard,
            Finset.subset_univ, true_and]
          constructor
          · rintro ⟨hQ4, hsub⟩
            exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
          · rintro rfl; exact ⟨hU4, subset_rfl⟩
        rw [heq, Finset.card_singleton]
      · simp only [ht3, ht2, ↓reduceIte]
        have hUge5 : 5 ≤ U.card := by
          have ht_le : t ≤ 3 := by
            rw [← ht]; exact (Finset.card_le_card Finset.inter_subset_left).trans h1.le
          omega
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro Q hQ hsub
        have hQ4 : Q.card = 4 := (Finset.mem_powersetCard.mp hQ).2
        have hle := Finset.card_le_card hsub
        omega
  have hterm : ∀ t ∈ Finset.range 4,
      ∑ p ∈ (hammingLayer n 3 ×ˢ hammingLayer n 3).filter
          (fun p => (supportOf p.1 ∩ supportOf p.2).card = t),
        ((Quads.filter (fun Q => supportOf p.1 ∪ supportOf p.2 ⊆ Q)).card : ℝ) *
          (boolToReal (f p.1) * boolToReal (f p.2)) =
      ((if t = 3 then n - 3 else if t = 2 then 1 else 0 : ℕ) : ℝ) *
        ((pairCount n 3 3 t : ℝ) * pairCorr f 3 3 t) := by
    intro t ht
    have ht3 : t ≤ 3 := by rw [Finset.mem_range] at ht; omega
    have hvalid : ValidTriple n 3 3 t := ⟨by omega, by omega, ht3, ht3, by omega⟩
    have hpc : (pairCount n 3 3 t : ℝ) ≠ 0 := by exact_mod_cast (pairCount_pos hvalid).ne'
    have hmul : (pairCount n 3 3 t : ℝ) * pairCorr f 3 3 t =
        ∑ p ∈ pairSet n 3 3 t, boolToReal (f p.1) * boolToReal (f p.2) := by
      unfold pairCorr; field_simp [hpc]
    rw [pairSet_eq_filter, hmul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p hp
    rw [hcntU t p hp]
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  have hdiag : (pairCount n 3 3 3 : ℝ) * pairCorr f 3 3 3 =
      realLayerSum (fun x => boolToReal (f x)) 3 := by
    rw [pairCorr_diag f (by omega), layerAvg, pairCount]
    have hc3 : (Nat.choose n 3 : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega : 3 ≤ n)).ne'
    simp only [Nat.choose_self, Nat.sub_self, Nat.choose_zero_right, mul_one]
    field_simp [hc3]
  rw [hdiag]
  simp only [show (0 : ℕ) ≠ 3 by omega, show (0 : ℕ) ≠ 2 by omega,
    show (1 : ℕ) ≠ 3 by omega, show (1 : ℕ) ≠ 2 by omega,
    show (2 : ℕ) ≠ 3 by omega, ↓reduceIte]
  push_cast; ring

/-! ### Part 4: Polymorphic Link-Graph Construction from Rigidity -/

lemma quadDeg3_eq_sum_four {n : ℕ} (f : BooleanFun n) {a b c d : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    quadDeg3 f ({a, b, c, d} : Finset (Fin n)) =
      boolToReal (f (indicator {a, b, c})) + boolToReal (f (indicator {a, b, d})) +
      boolToReal (f (indicator {a, c, d})) + boolToReal (f (indicator {b, c, d})) := by
  set Q : Finset (Fin n) := {a, b, c, d}
  have hfilt : (hammingLayer n 3).filter (fun x => supportOf x ⊆ Q) =
      {indicator {a, b, c}, indicator {a, b, d}, indicator {a, c, d}, indicator {b, c, d}} := by
    ext x
    simp only [Finset.mem_filter, mem_hammingLayer_iff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx3, hsub⟩
      have hcardQ : Q.card = 4 := card_four_finset hab hac had hbc hbd hcd
      have hsdiff : (Q \ supportOf x).card = 1 := by
        rw [Finset.card_sdiff_of_subset hsub, hcardQ, hx3]
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hsdiff
      have hzQ : z ∈ Q := (Finset.mem_sdiff.mp (by rw [hz]; exact Finset.mem_singleton_self z)).1
      have hsupp : supportOf x = Q.erase z := by
        ext k
        simp only [Finset.mem_erase]
        constructor
        · intro hk
          refine ⟨?_, hsub hk⟩
          intro hkz; subst hkz
          exact (Finset.mem_sdiff.mp (by rw [hz]; exact Finset.mem_singleton_self k)).2 hk
        · rintro ⟨hkz, hkQ⟩
          by_contra hnot
          have : k ∈ Q \ supportOf x := Finset.mem_sdiff.mpr ⟨hkQ, hnot⟩
          rw [hz, Finset.mem_singleton] at this
          exact hkz this
      have hxind : x = indicator (Q.erase z) := by rw [← indicator_supportOf x, hsupp]
      rw [hxind]
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hzQ
      rcases hzQ with rfl | rfl | rfl | rfl
      · right; right; right; congr 1
        ext k; simp only [Q, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hkne, rfl | rfl | rfl | rfl⟩
          · exact absurd rfl hkne
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
        · rintro (rfl | rfl | rfl)
          · exact ⟨hab.symm, Or.inr (Or.inl rfl)⟩
          · exact ⟨hac.symm, Or.inr (Or.inr (Or.inl rfl))⟩
          · exact ⟨had.symm, Or.inr (Or.inr (Or.inr rfl))⟩
      · right; right; left; congr 1
        ext k; simp only [Q, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hkne, rfl | rfl | rfl | rfl⟩
          · exact Or.inl rfl
          · exact absurd rfl hkne
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
        · rintro (rfl | rfl | rfl)
          · exact ⟨hab, Or.inl rfl⟩
          · exact ⟨hbc.symm, Or.inr (Or.inr (Or.inl rfl))⟩
          · exact ⟨hbd.symm, Or.inr (Or.inr (Or.inr rfl))⟩
      · right; left; congr 1
        ext k; simp only [Q, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hkne, rfl | rfl | rfl | rfl⟩
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact absurd rfl hkne
          · exact Or.inr (Or.inr rfl)
        · rintro (rfl | rfl | rfl)
          · exact ⟨hac, Or.inl rfl⟩
          · exact ⟨hbc, Or.inr (Or.inl rfl)⟩
          · exact ⟨hcd.symm, Or.inr (Or.inr (Or.inr rfl))⟩
      · left; congr 1
        ext k; simp only [Q, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hkne, rfl | rfl | rfl | rfl⟩
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact absurd rfl hkne
        · rintro (rfl | rfl | rfl)
          · exact ⟨had, Or.inl rfl⟩
          · exact ⟨hbd, Or.inr (Or.inl rfl)⟩
          · exact ⟨hcd, Or.inr (Or.inr (Or.inl rfl))⟩
    · rintro (rfl | rfl | rfl | rfl) <;> refine ⟨?_, ?_⟩ <;> (try rw [supportOf_indicator])
      · simp [hab, hac, hbc]
      · intro k hk; simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hk ⊢; tauto
      · simp [hab, had, hbd]
      · intro k hk; simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hk ⊢; tauto
      · simp [hac, had, hcd]
      · intro k hk; simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hk ⊢; tauto
      · simp [hbc, hbd, hcd]
      · intro k hk; simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hk ⊢; tauto
  have hne : ∀ (S T : Finset (Fin n)), S ≠ T → indicator S ≠ indicator T := by
    intro S T hST hEq; exact hST (by simpa [supportOf_indicator] using congrArg supportOf hEq)
  have h12 : indicator ({a, b, c} : Finset (Fin n)) ≠ indicator {a, b, d} := by
    apply hne; intro h; have : c ∈ ({a, b, d} : Finset (Fin n)) := by rw [← h]; simp
    simp [hac.symm, hbc.symm, hcd] at this
  have h13 : indicator ({a, b, c} : Finset (Fin n)) ≠ indicator {a, c, d} := by
    apply hne; intro h; have : b ∈ ({a, c, d} : Finset (Fin n)) := by rw [← h]; simp
    simp [hab.symm, hbc, hbd] at this
  have h14 : indicator ({a, b, c} : Finset (Fin n)) ≠ indicator {b, c, d} := by
    apply hne; intro h; have : a ∈ ({b, c, d} : Finset (Fin n)) := by rw [← h]; simp
    simp [hab, hac, had] at this
  have h23 : indicator ({a, b, d} : Finset (Fin n)) ≠ indicator {a, c, d} := by
    apply hne; intro h; have : b ∈ ({a, c, d} : Finset (Fin n)) := by rw [← h]; simp
    simp [hab.symm, hbc, hbd] at this
  have h24 : indicator ({a, b, d} : Finset (Fin n)) ≠ indicator {b, c, d} := by
    apply hne; intro h; have : a ∈ ({b, c, d} : Finset (Fin n)) := by rw [← h]; simp
    simp [hab, hac, had] at this
  have h34 : indicator ({a, c, d} : Finset (Fin n)) ≠ indicator {b, c, d} := by
    apply hne; intro h; have : a ∈ ({b, c, d} : Finset (Fin n)) := by rw [← h]; simp
    simp [hab, hac, had] at this
  rw [quadDeg3, hfilt, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · ring
  · simp [h34]
  · simp [h23, h24]
  · simp [h12, h13, h14]

/-- **Universal Link-Graph Rigidity Reduction**:
If `f : BooleanFun (m + 1)` satisfies `pairDeg3 f P = d0` for every 2-subset `P` and
`quadDeg3 f Q = 2 + 2 f(Q)` for every 4-subset `Q`, with `d0 + r + 1 = m`, then there exists an
`r`-regular, triangle-free, induced-`2K₂`-free simple graph on `Fin m`. -/
theorem exists_reg_trifree_2k2free_of_rigidity {m d0 r : ℕ} (hm : d0 + r + 1 = m)
    (f : BooleanFun (m + 1))
    (hpair : ∀ P ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin (m + 1))),
      pairDeg3 f P = (d0 : ℝ))
    (hquad : ∀ Q ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin (m + 1))),
      quadDeg3 f Q = 2 + 2 * boolToReal (f (indicator Q))) :
    ∃ adj : Fin m → Fin m → Bool,
      (∀ u, adj u u = false) ∧
      (∀ u v, adj u v = adj v u) ∧
      (∀ u, (Finset.univ.filter (fun w => adj u w = true)).card = r) ∧
      (∀ u v w, adj u v = true → adj v w = true → adj u w = false) ∧
      (∀ a b c d, a ≠ c → a ≠ d → b ≠ c → b ≠ d →
        adj a b = true → adj c d = true →
        adj a c = true ∨ adj a d = true ∨ adj b c = true ∨ adj b d = true) := by
  let c0 : Fin (m + 1) := Fin.last m
  let adj : Fin m → Fin m → Bool := fun u v =>
    decide (u ≠ v) && !(f (indicator ({u.castSucc, v.castSucc, c0} : Finset (Fin (m + 1)))))
  have hc0_ne : ∀ u : Fin m, u.castSucc ≠ c0 := fun u => Fin.castSucc_ne_last u
  have hcast_inj : ∀ u v : Fin m, u.castSucc = v.castSucc → u = v :=
    fun _ _ h => Fin.castSucc_injective m h
  have hadj_iff : ∀ u v : Fin m,
      adj u v = true ↔ u ≠ v ∧ f (indicator ({u.castSucc, v.castSucc, c0} : Finset (Fin (m + 1)))) = false := by
    intro u v
    simp only [adj, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  have hirrefl : ∀ u : Fin m, adj u u = false := by intro u; simp [adj]
  have hsymm : ∀ u v : Fin m, adj u v = adj v u := by
    intro u v
    have hset : ({u.castSucc, v.castSucc, c0} : Finset (Fin (m + 1))) = {v.castSucc, u.castSucc, c0} :=
      Finset.insert_comm u.castSucc v.castSucc {c0}
    by_cases huv : u = v
    · subst huv; rfl
    · have hvu : v ≠ u := Ne.symm huv
      simp [adj, huv, hvu, hset]
  have hreg : ∀ u : Fin m, (Finset.univ.filter (fun w => adj u w = true)).card = r := by
    intro u
    let P : Finset (Fin (m + 1)) := {u.castSucc, c0}
    have hPmem : P ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin (m + 1))) := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, by simp [P, hc0_ne u]⟩
    have hd0_eq : pairDeg3 f P = (d0 : ℝ) := hpair P hPmem
    have hsum_eq : pairDeg3 f P =
        ∑ w ∈ (Finset.univ : Finset (Fin m)).erase u,
          boolToReal (f (indicator ({u.castSucc, w.castSucc, c0} : Finset (Fin (m + 1))))) := by
      unfold pairDeg3
      symm
      apply Finset.sum_nbij (fun w => indicator ({u.castSucc, w.castSucc, c0} : Finset (Fin (m + 1))))
      · intro w hw
        have hwu : w ≠ u := (Finset.mem_erase.mp hw).1
        rw [Finset.mem_filter, mem_hammingLayer_iff]
        refine ⟨?_, ?_⟩
        · rw [supportOf_indicator]
          have h1 : u.castSucc ≠ w.castSucc := fun h => hwu (hcast_inj u w h).symm
          simp [h1, hc0_ne u, hc0_ne w]
        · rw [supportOf_indicator]
          intro k hk
          simp only [P, Finset.mem_insert, Finset.mem_singleton] at hk ⊢
          rcases hk with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr rfl)
      · intro w₁ hw₁ w₂ _ hEq
        have hw₁u : w₁ ≠ u := (Finset.mem_erase.mp hw₁).1
        have hs := congrArg supportOf hEq
        simp only [supportOf_indicator] at hs
        have hmem : w₁.castSucc ∈ ({u.castSucc, w₂.castSucc, c0} : Finset (Fin (m + 1))) := by
          rw [← hs]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h | h
        · exact absurd (hcast_inj w₁ u h) hw₁u
        · exact hcast_inj w₁ w₂ h
        · exact absurd h (hc0_ne w₁)
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_filter, mem_hammingLayer_iff] at hx
        obtain ⟨hx3, hPsub⟩ := hx
        have hPcard : P.card = 2 := by simp [P, hc0_ne u]
        have hsdiff : (supportOf x \ P).card = 1 := by
          rw [Finset.card_sdiff_of_subset hPsub, hx3, hPcard]
        obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hsdiff
        have hz_mem : z ∈ supportOf x \ P := by rw [hz]; exact Finset.mem_singleton_self z
        obtain ⟨hzx, hz_notP⟩ := Finset.mem_sdiff.mp hz_mem
        have hzc0 : z ≠ c0 := fun h => hz_notP (by simp [P, h])
        have hzu : z ≠ u.castSucc := fun h => hz_notP (by simp [P, h])
        have hzlt : z.val < m := by
          have : z.val < m + 1 := z.isLt
          have hne : z.val ≠ m := fun h => hzc0 (Fin.ext h)
          omega
        let w : Fin m := ⟨z.val, hzlt⟩
        have hw_cast : w.castSucc = z := Fin.ext rfl
        have hwu : w ≠ u := fun h => hzu (by rw [← hw_cast, h])
        refine ⟨w, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hwu, Finset.mem_univ w⟩), ?_⟩
        have hsupp : supportOf x = {u.castSucc, w.castSucc, c0} := by
          ext k
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro hkx
            by_cases hkP : k ∈ P
            · simp only [P, Finset.mem_insert, Finset.mem_singleton] at hkP
              rcases hkP with rfl | rfl
              · exact Or.inl rfl
              · exact Or.inr (Or.inr rfl)
            · right; left
              have : k ∈ supportOf x \ P := Finset.mem_sdiff.mpr ⟨hkx, hkP⟩
              rw [hz, Finset.mem_singleton] at this; rw [hw_cast, this]
          · rintro (rfl | rfl | rfl)
            · exact hPsub (by simp [P])
            · rw [hw_cast]; exact hzx
            · exact hPsub (by simp [P])
        dsimp only
        rw [← hsupp, indicator_supportOf]
      · intro _ _; rfl
    have hcard_erase : ((Finset.univ : Finset (Fin m)).erase u).card = m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]
    have hcount_real :
        (((Finset.univ : Finset (Fin m)).filter (fun w => adj u w = true)).card : ℝ) +
          pairDeg3 f P = ((m - 1 : ℕ) : ℝ) := by
      rw [hsum_eq]
      have hfilt_eq : (Finset.univ : Finset (Fin m)).filter (fun w => adj u w = true) =
          ((Finset.univ : Finset (Fin m)).erase u).filter
            (fun w => f (indicator ({u.castSucc, w.castSucc, c0} : Finset (Fin (m + 1)))) = false) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true, Finset.mem_erase, hadj_iff]
        exact ⟨fun ⟨h1, h2⟩ => ⟨Ne.symm h1, h2⟩, fun ⟨h1, h2⟩ => ⟨Ne.symm h1, h2⟩⟩
      rw [hfilt_eq, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      simp only [Nat.cast_one]
      rw [← Finset.sum_add_distrib]
      calc ∑ w ∈ (Finset.univ : Finset (Fin m)).erase u,
            ((if f (indicator ({u.castSucc, w.castSucc, c0} : Finset (Fin (m + 1)))) = false then (1 : ℝ) else 0) +
              boolToReal (f (indicator ({u.castSucc, w.castSucc, c0} : Finset (Fin (m + 1))))))
          = ∑ _w ∈ (Finset.univ : Finset (Fin m)).erase u, (1 : ℝ) := by
            apply Finset.sum_congr rfl; intro w _
            cases f (indicator ({u.castSucc, w.castSucc, c0} : Finset (Fin (m + 1)))) <;>
              norm_num [boolToReal]
        _ = ((m - 1 : ℕ) : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard_erase]
    have hm1 : m - 1 = d0 + r := by omega
    rw [hd0_eq, hm1, Nat.cast_add] at hcount_real
    have hcard_r : (((Finset.univ : Finset (Fin m)).filter (fun w => adj u w = true)).card : ℝ) = (r : ℝ) := by
      linarith
    exact_mod_cast hcard_r
  have htrifree : ∀ u v w : Fin m, adj u v = true → adj v w = true → adj u w = false := by
    intro u v w huv hvw
    by_contra hne
    have huw : adj u w = true := Bool.eq_true_of_not_eq_false hne
    obtain ⟨huv_ne, hfuv⟩ := (hadj_iff u v).mp huv
    obtain ⟨hvw_ne, hfvw⟩ := (hadj_iff v w).mp hvw
    obtain ⟨huw_ne, hfuw⟩ := (hadj_iff u w).mp huw
    have hab : u.castSucc ≠ v.castSucc := fun h => huv_ne (hcast_inj u v h)
    have hac : u.castSucc ≠ w.castSucc := fun h => huw_ne (hcast_inj u w h)
    have hbc : v.castSucc ≠ w.castSucc := fun h => hvw_ne (hcast_inj v w h)
    let Q : Finset (Fin (m + 1)) := {u.castSucc, v.castSucc, w.castSucc, c0}
    have hQmem : Q ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin (m + 1))) := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, card_four_finset hab hac (hc0_ne u) hbc (hc0_ne v) (hc0_ne w)⟩
    have hrig := hquad Q hQmem
    have hsum4 := quadDeg3_eq_sum_four f hab hac (hc0_ne u) hbc (hc0_ne v) (hc0_ne w)
    change quadDeg3 f Q = _ at hsum4
    rw [hfuv, hfuw, hfvw] at hsum4
    have hle1 : quadDeg3 f Q ≤ 1 := by
      rw [hsum4]
      cases f (indicator ({u.castSucc, v.castSucc, w.castSucc} : Finset (Fin (m + 1)))) <;>
        norm_num [boolToReal]
    have hge2 : 2 ≤ quadDeg3 f Q := by
      rw [hrig]
      cases f (indicator Q) <;> norm_num [boolToReal]
    linarith
  have htriple_zero : ∀ x y z : Fin m,
      x ≠ z → y ≠ z → adj x y = true → adj x z = false → adj y z = false →
      f (indicator ({x.castSucc, y.castSucc, z.castSucc} : Finset (Fin (m + 1)))) = false := by
    intro x y z hxz hyz hxy hxz_f hyz_f
    obtain ⟨hxy_ne, hfxy⟩ := (hadj_iff x y).mp hxy
    have hfxz : f (indicator ({x.castSucc, z.castSucc, c0} : Finset (Fin (m + 1)))) = true := by
      cases h : f (indicator ({x.castSucc, z.castSucc, c0} : Finset (Fin (m + 1))))
      · exfalso; have := (hadj_iff x z).mpr ⟨hxz, h⟩; rw [hxz_f] at this; exact Bool.noConfusion this
      · rfl
    have hfyz : f (indicator ({y.castSucc, z.castSucc, c0} : Finset (Fin (m + 1)))) = true := by
      cases h : f (indicator ({y.castSucc, z.castSucc, c0} : Finset (Fin (m + 1))))
      · exfalso; have := (hadj_iff y z).mpr ⟨hyz, h⟩; rw [hyz_f] at this; exact Bool.noConfusion this
      · rfl
    have hab : x.castSucc ≠ y.castSucc := fun h => hxy_ne (hcast_inj x y h)
    have hac : x.castSucc ≠ z.castSucc := fun h => hxz (hcast_inj x z h)
    have hbc : y.castSucc ≠ z.castSucc := fun h => hyz (hcast_inj y z h)
    let Q : Finset (Fin (m + 1)) := {x.castSucc, y.castSucc, z.castSucc, c0}
    have hQmem : Q ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin (m + 1))) := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, card_four_finset hab hac (hc0_ne x) hbc (hc0_ne y) (hc0_ne z)⟩
    have hrig := hquad Q hQmem
    have hsum4 := quadDeg3_eq_sum_four f hab hac (hc0_ne x) hbc (hc0_ne y) (hc0_ne z)
    change quadDeg3 f Q = _ at hsum4
    rw [hfxy, hfxz, hfyz] at hsum4
    cases hval : f (indicator ({x.castSucc, y.castSucc, z.castSucc} : Finset (Fin (m + 1))))
    · rfl
    · exfalso
      rw [hval] at hsum4
      cases hfQ : f (indicator Q) <;> rw [hfQ] at hrig <;> norm_num [boolToReal] at hsum4 hrig <;> linarith
  have h2k2free : ∀ a b c d : Fin m,
      a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      adj a b = true → adj c d = true →
      adj a c = true ∨ adj a d = true ∨ adj b c = true ∨ adj b d = true := by
    intro a b c d hac had hbc hbd hab hcd
    by_contra hnone
    push Not at hnone
    obtain ⟨hac_f, had_f, hbc_f, hbd_f⟩ := hnone
    have hac_b : adj a c = false := Bool.eq_false_iff.mpr hac_f
    have had_b : adj a d = false := Bool.eq_false_iff.mpr had_f
    have hbc_b : adj b c = false := Bool.eq_false_iff.mpr hbc_f
    have hbd_b : adj b d = false := Bool.eq_false_iff.mpr hbd_f
    have hca_b : adj c a = false := by rw [hsymm]; exact hac_b
    have hda_b : adj d a = false := by rw [hsymm]; exact had_b
    have hcb_b : adj c b = false := by rw [hsymm]; exact hbc_b
    have hdb_b : adj d b = false := by rw [hsymm]; exact hbd_b
    have hab_ne : a ≠ b := ((hadj_iff a b).mp hab).1
    have hcd_ne : c ≠ d := ((hadj_iff c d).mp hcd).1
    have hf_abc := htriple_zero a b c hac hbc hab hac_b hbc_b
    have hf_abd := htriple_zero a b d had hbd hab had_b hbd_b
    have hf_cda := htriple_zero c d a hac.symm had.symm hcd hca_b hda_b
    have hf_cdb := htriple_zero c d b hbc.symm hbd.symm hcd hcb_b hdb_b
    have hset_acd : ({c.castSucc, d.castSucc, a.castSucc} : Finset (Fin (m + 1))) =
        {a.castSucc, c.castSucc, d.castSucc} := by
      rw [Finset.pair_comm d.castSucc a.castSucc, Finset.insert_comm c.castSucc a.castSucc]
    have hset_bcd : ({c.castSucc, d.castSucc, b.castSucc} : Finset (Fin (m + 1))) =
        {b.castSucc, c.castSucc, d.castSucc} := by
      rw [Finset.pair_comm d.castSucc b.castSucc, Finset.insert_comm c.castSucc b.castSucc]
    rw [hset_acd] at hf_cda
    rw [hset_bcd] at hf_cdb
    have h12 : a.castSucc ≠ b.castSucc := fun h => hab_ne (hcast_inj a b h)
    have h13 : a.castSucc ≠ c.castSucc := fun h => hac (hcast_inj a c h)
    have h14 : a.castSucc ≠ d.castSucc := fun h => had (hcast_inj a d h)
    have h23 : b.castSucc ≠ c.castSucc := fun h => hbc (hcast_inj b c h)
    have h24 : b.castSucc ≠ d.castSucc := fun h => hbd (hcast_inj b d h)
    have h34 : c.castSucc ≠ d.castSucc := fun h => hcd_ne (hcast_inj c d h)
    let Q5 : Finset (Fin (m + 1)) := {a.castSucc, b.castSucc, c.castSucc, d.castSucc}
    have hQ5mem : Q5 ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin (m + 1))) := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, card_four_finset h12 h13 h14 h23 h24 h34⟩
    have hrig := hquad Q5 hQ5mem
    have hsum4 := quadDeg3_eq_sum_four f h12 h13 h14 h23 h24 h34
    change quadDeg3 f Q5 = _ at hsum4
    rw [hf_abc, hf_abd, hf_cda, hf_cdb] at hsum4
    cases hfQ5 : f (indicator Q5) <;> rw [hfQ5] at hrig <;> norm_num [boolToReal] at hsum4 hrig <;> linarith
  exact ⟨adj, hirrefl, hsymm, hreg, htrifree, h2k2free⟩

end DegreeSensitivity
