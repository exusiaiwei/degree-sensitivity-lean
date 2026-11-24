module

public import DegreeSensitivity.Symmetrisation

@[expose] public section

/-!
# Terwilliger Pair-Correlation Algebra for Boolean Functions

Given a Boolean function `f : BooleanFun n`, we define the Terwilliger pair-correlation
variables

  `pairCorr f i j t = E_{|x| = i, |y| = j, |x ∩ y| = t}[f(x) f(y)]`

and prove all exact identities and inequalities used by both:
1. The **Subset-J Binomial-Basis Terwilliger LP** (proving `B_7 ≤ 28`, `B_8 ≤ 36`, ...), and
2. The **Joint Terwilliger LP + SOS proof** of `(n = 15, d = 5)` impossibility (`B_5 ≤ 14`).

Specifically, we prove:
- Exact cardinality `|pairSet n i j t| = C(n, i) * C(i, t) * C(n - i, j - t)` and symmetry.
- Bounds `0 ≤ pairCorr f i j t ≤ 1` and all three McCormick/Fréchet inequalities
  (`m ≤ p_i`, `m ≤ p_j`, `p_i + p_j - m ≤ 1`).
- Diagonal and boundary equalities (`m(i,i,i) = p_i`, `m(0,j,0) = 0`, `m(1,j,1) = p_j`,
  `m(1,j,0) = p_j`).
- **Bivariate Symmetrisation Theorem** (`pairCorr_eq_bivar_binomial_sum`): for any `j ≤ n`,
  `pairCorr f (a + b) j a = ∑_{r + s ≤ d} c_{j, r, s} C(a, r) C(b, s)`.
- Univariate and bivariate `(d + 1)`-th finite-difference vanishing identities.
- Layer-product identity `∑_t C(i, t) C(n - i, j - t) m(i, j, t) = C(n, j) p_i p_j`.
-/

namespace DegreeSensitivity

open scoped BigOperators

/-- Validity predicate for a Terwilliger triple `(i, j, t)` in dimension `n`. -/
def ValidTriple (n i j t : ℕ) : Prop :=
  i ≤ n ∧ j ≤ n ∧ t ≤ i ∧ t ≤ j ∧ i + j ≤ n + t

lemma ValidTriple.symm {n i j t : ℕ} (h : ValidTriple n i j t) : ValidTriple n j i t := by
  obtain ⟨hi, hj, hti, htj, hij⟩ := h
  exact ⟨hj, hi, htj, hti, by omega⟩

private lemma finset_inter_union_sdiff {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∩ B) ∪ (A \ B) = A := by
  ext x; by_cases hx : x ∈ B <;> simp [hx]

/-- The set of pairs `(x, y)` in `{0, 1}^n × {0, 1}^n` with `|x| = i`, `|y| = j`, `|x ∩ y| = t`. -/
def pairSet (n i j t : ℕ) : Finset ((Fin n → Bool) × (Fin n → Bool)) :=
  (hammingLayer n i ×ˢ hammingLayer n j).filter (fun p => (supportOf p.1 ∩ supportOf p.2).card = t)

/-- Closed-form cardinality of `pairSet n i j t`. -/
def pairCount (n i j t : ℕ) : ℕ :=
  Nat.choose n i * Nat.choose i t * Nat.choose (n - i) (j - t)

lemma pairCount_pos {n i j t : ℕ} (h : ValidTriple n i j t) : 0 < pairCount n i j t := by
  obtain ⟨hi, _, hti, htj, hij⟩ := h
  unfold pairCount
  have h1 : 0 < Nat.choose n i := Nat.choose_pos hi
  have h2 : 0 < Nat.choose i t := Nat.choose_pos hti
  have h3 : 0 < Nat.choose (n - i) (j - t) := Nat.choose_pos (by omega)
  positivity

/-- For any fixed `x` of weight `i`, the number of `y` of weight `j` intersecting `x` in `t` bits
is `C(i, t) * C(n - i, j - t)`. -/
lemma card_slice_right {n i j t : ℕ} (x : Fin n → Bool) (hx : (supportOf x).card = i)
    (h : ValidTriple n i j t) :
    ((hammingLayer n j).filter (fun y => (supportOf x ∩ supportOf y).card = t)).card =
      Nat.choose i t * Nat.choose (n - i) (j - t) := by
  classical
  obtain ⟨_, _, _, htj, _⟩ := h
  let A := supportOf x
  have hAcard : A.card = i := hx
  have hAc_card : Aᶜ.card = n - i := by rw [Finset.card_compl, Fintype.card_fin, hAcard]
  have hbij : ((hammingLayer n j).filter (fun y => (A ∩ supportOf y).card = t)).card =
      (Finset.powersetCard t A ×ˢ Finset.powersetCard (j - t) Aᶜ).card := by
    apply Finset.card_bij (fun y _ => (A ∩ supportOf y, supportOf y \ A))
    · intro y hy
      obtain ⟨hyL, hyT⟩ := Finset.mem_filter.mp hy
      have hyCard : (supportOf y).card = j := (Finset.mem_filter.mp hyL).2
      rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
      refine ⟨⟨Finset.inter_subset_left, hyT⟩, ⟨?_, ?_⟩⟩
      · intro k hk; exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hk).2
      · rw [Finset.card_sdiff, hyCard, hyT]
    · intro y₁ _ y₂ _ hEq
      have h1 : A ∩ supportOf y₁ = A ∩ supportOf y₂ := congrArg Prod.fst hEq
      have h2 : supportOf y₁ \ A = supportOf y₂ \ A := congrArg Prod.snd hEq
      have hsupp : supportOf y₁ = supportOf y₂ := by
        calc supportOf y₁ = (supportOf y₁ ∩ A) ∪ (supportOf y₁ \ A) := (finset_inter_union_sdiff _ _).symm
          _ = (A ∩ supportOf y₁) ∪ (supportOf y₁ \ A) := by rw [Finset.inter_comm]
          _ = (A ∩ supportOf y₂) ∪ (supportOf y₂ \ A) := by rw [h1, h2]
          _ = (supportOf y₂ ∩ A) ∪ (supportOf y₂ \ A) := by rw [Finset.inter_comm]
          _ = supportOf y₂ := finset_inter_union_sdiff _ _
      have := congrArg indicator hsupp
      simpa [indicator_supportOf] using this
    · rintro ⟨U, V⟩ hUV
      rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard] at hUV
      obtain ⟨⟨hUA, hUcard⟩, ⟨hVAc, hVcard⟩⟩ := hUV
      have hdisj : Disjoint U V := by
        rw [Finset.disjoint_left]; intro k hkU hkV
        exact (Finset.mem_compl.mp (hVAc hkV)) (hUA hkU)
      have hAV : Disjoint A V := by
        rw [Finset.disjoint_left]; intro k hkA hkV
        exact (Finset.mem_compl.mp (hVAc hkV)) hkA
      have hAU : A ∩ (U ∪ V) = U := by
        rw [Finset.inter_union_distrib_left, Finset.inter_eq_right.mpr hUA,
          Finset.disjoint_iff_inter_eq_empty.mp hAV, Finset.union_empty]
      have hUVs : (U ∪ V) \ A = V := by
        rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_empty_iff_subset.mpr hUA, Finset.empty_union,
          Finset.sdiff_eq_self_of_disjoint hAV.symm]
      refine ⟨indicator (U ∪ V), ?_, ?_⟩
      · rw [Finset.mem_filter, hammingLayer, Finset.mem_filter]
        refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · rw [supportOf_indicator, Finset.card_union_of_disjoint hdisj, hUcard, hVcard]; omega
        · rw [supportOf_indicator, hAU, hUcard]
      · simp [supportOf_indicator, hAU, hUVs]
  rw [hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard, hAcard, hAc_card]

/-- Cardinality of `pairSet n i j t`. -/
lemma card_pairSet {n i j t : ℕ} (h : ValidTriple n i j t) :
    (pairSet n i j t).card = pairCount n i j t := by
  classical
  have hsum : (pairSet n i j t).card =
      ∑ x ∈ hammingLayer n i,
        ((hammingLayer n j).filter (fun y => (supportOf x ∩ supportOf y).card = t)).card := by
    rw [pairSet, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro x _
    dsimp only
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hsum]
  calc ∑ x ∈ hammingLayer n i,
        ((hammingLayer n j).filter (fun y => (supportOf x ∩ supportOf y).card = t)).card
      = ∑ _x ∈ hammingLayer n i, (Nat.choose i t * Nat.choose (n - i) (j - t)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact card_slice_right x (Finset.mem_filter.mp hx).2 h
    _ = (hammingLayer n i).card * (Nat.choose i t * Nat.choose (n - i) (j - t)) := by
        rw [Finset.sum_const]; rfl
    _ = pairCount n i j t := by rw [card_hammingLayer, pairCount, mul_assoc]

/-- Symmetry of `pairCount` in `(i, j)`. -/
lemma pairCount_symm {n i j t : ℕ} (h : ValidTriple n i j t) :
    pairCount n i j t = pairCount n j i t := by
  rw [← card_pairSet h, ← card_pairSet h.symm]
  apply Finset.card_bij (fun p _ => (p.2, p.1))
  · intro p hp
    simp only [pairSet, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, by rw [Finset.inter_comm]; exact hp.2⟩
  · intro p₁ _ p₂ _ hEq
    exact Prod.ext (congrArg Prod.snd hEq) (congrArg Prod.fst hEq)
  · intro p hp
    refine ⟨(p.2, p.1), ?_, rfl⟩
    simp only [pairSet, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, by rw [Finset.inter_comm]; exact hp.2⟩

/-- The Terwilliger pair correlation `m_f(i, j, t) = E_{|x|=i, |y|=j, |x ∩ y|=t}[f(x) f(y)]`. -/
noncomputable def pairCorr {n : ℕ} (f : BooleanFun n) (i j t : ℕ) : ℝ :=
  (∑ p ∈ pairSet n i j t, boolToReal (f p.1) * boolToReal (f p.2)) / (pairCount n i j t : ℝ)

/-- Symmetry of `pairCorr`: `m_f(i, j, t) = m_f(j, i, t)`. -/
theorem pairCorr_symm {n i j t : ℕ} (f : BooleanFun n) (h : ValidTriple n i j t) :
    pairCorr f i j t = pairCorr f j i t := by
  unfold pairCorr
  rw [pairCount_symm h]
  congr 1
  apply Finset.sum_nbij (fun p => (p.2, p.1))
  · intro p hp
    simp only [pairSet, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, by rw [Finset.inter_comm]; exact hp.2⟩
  · intro p₁ _ p₂ _ hEq
    exact Prod.ext (congrArg Prod.snd hEq) (congrArg Prod.fst hEq)
  · intro p hp
    refine ⟨(p.2, p.1), ?_, rfl⟩
    simp only [Finset.mem_coe, pairSet, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, by rw [Finset.inter_comm]; exact hp.2⟩
  · intro p _; ring

/-- Helper: average of `f p.1` over `pairSet n i j t` equals `layerAvg f i`. -/
lemma sum_pairSet_left {n i j t : ℕ} (f : BooleanFun n) (h : ValidTriple n i j t) :
    ∑ p ∈ pairSet n i j t, boolToReal (f p.1) =
      (pairCount n i j t : ℝ) * layerAvg (fun x => boolToReal (f x)) i := by
  classical
  have h1 : ∑ p ∈ pairSet n i j t, boolToReal (f p.1) =
      ∑ x ∈ hammingLayer n i,
        boolToReal (f x) * (((hammingLayer n j).filter (fun y => (supportOf x ∩ supportOf y).card = t)).card : ℝ) := by
    rw [pairSet, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro x _
    dsimp only
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [h1]
  have h2 : ∑ x ∈ hammingLayer n i,
      boolToReal (f x) * (((hammingLayer n j).filter (fun y => (supportOf x ∩ supportOf y).card = t)).card : ℝ) =
      (Nat.choose i t * Nat.choose (n - i) (j - t) : ℝ) * realLayerSum (fun x => boolToReal (f x)) i := by
    rw [realLayerSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [card_slice_right x (Finset.mem_filter.mp hx).2 h]
    push_cast
    ring
  rw [h2, layerAvg, pairCount]
  have hci : (Nat.choose n i : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos h.1).ne'
  push_cast
  field_simp [hci]

/-- Helper: average of `f p.2` over `pairSet n i j t` equals `layerAvg f j`. -/
lemma sum_pairSet_right {n i j t : ℕ} (f : BooleanFun n) (h : ValidTriple n i j t) :
    ∑ p ∈ pairSet n i j t, boolToReal (f p.2) =
      (pairCount n i j t : ℝ) * layerAvg (fun x => boolToReal (f x)) j := by
  have hswap : ∑ p ∈ pairSet n i j t, boolToReal (f p.2) =
      ∑ p ∈ pairSet n j i t, boolToReal (f p.1) := by
    apply Finset.sum_nbij (fun p => (p.2, p.1))
    · intro p hp
      simp only [pairSet, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, by rw [Finset.inter_comm]; exact hp.2⟩
    · intro p₁ _ p₂ _ hEq
      exact Prod.ext (congrArg Prod.snd hEq) (congrArg Prod.fst hEq)
    · intro p hp
      refine ⟨(p.2, p.1), ?_, rfl⟩
      simp only [Finset.mem_coe, pairSet, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, by rw [Finset.inter_comm]; exact hp.2⟩
    · intro _ _; rfl
  rw [hswap, sum_pairSet_left f h.symm, pairCount_symm h]

lemma pairCorr_nonneg {n i j t : ℕ} (f : BooleanFun n) : 0 ≤ pairCorr f i j t := by
  unfold pairCorr
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro p _
    cases f p.1 <;> cases f p.2 <;> norm_num [boolToReal]
  · exact Nat.cast_nonneg _

lemma pairCorr_le_one {n i j t : ℕ} (f : BooleanFun n) (h : ValidTriple n i j t) :
    pairCorr f i j t ≤ 1 := by
  unfold pairCorr
  have hpos : (0 : ℝ) < (pairCount n i j t : ℝ) := by exact_mod_cast pairCount_pos h
  rw [div_le_one hpos]
  calc ∑ p ∈ pairSet n i j t, boolToReal (f p.1) * boolToReal (f p.2)
      ≤ ∑ _p ∈ pairSet n i j t, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p _
        cases f p.1 <;> cases f p.2 <;> norm_num [boolToReal]
    _ = ((pairSet n i j t).card : ℝ) := by simp
    _ = (pairCount n i j t : ℝ) := by exact_mod_cast card_pairSet h

lemma pairCorr_le_left {n i j t : ℕ} (f : BooleanFun n) (h : ValidTriple n i j t) :
    pairCorr f i j t ≤ layerAvg (fun x => boolToReal (f x)) i := by
  unfold pairCorr
  have hpos : (0 : ℝ) < (pairCount n i j t : ℝ) := by exact_mod_cast pairCount_pos h
  rw [div_le_iff₀ hpos, mul_comm, ← sum_pairSet_left f h]
  apply Finset.sum_le_sum
  intro p _
  cases f p.1 <;> cases f p.2 <;> norm_num [boolToReal]

lemma pairCorr_le_right {n i j t : ℕ} (f : BooleanFun n) (h : ValidTriple n i j t) :
    pairCorr f i j t ≤ layerAvg (fun x => boolToReal (f x)) j := by
  rw [pairCorr_symm f h]
  exact pairCorr_le_left f h.symm

lemma pairCorr_frechet {n i j t : ℕ} (f : BooleanFun n) (h : ValidTriple n i j t) :
    layerAvg (fun x => boolToReal (f x)) i + layerAvg (fun x => boolToReal (f x)) j -
      pairCorr f i j t ≤ 1 := by
  have hpos : (0 : ℝ) < (pairCount n i j t : ℝ) := by exact_mod_cast pairCount_pos h
  have hcard : ((pairSet n i j t).card : ℝ) = (pairCount n i j t : ℝ) := by
    exact_mod_cast card_pairSet h
  have hsum : ∑ p ∈ pairSet n i j t,
      (boolToReal (f p.1) + boolToReal (f p.2) - boolToReal (f p.1) * boolToReal (f p.2)) ≤
      (pairCount n i j t : ℝ) := by
    calc ∑ p ∈ pairSet n i j t,
          (boolToReal (f p.1) + boolToReal (f p.2) - boolToReal (f p.1) * boolToReal (f p.2))
        ≤ ∑ _p ∈ pairSet n i j t, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro p _
          cases f p.1 <;> cases f p.2 <;> norm_num [boolToReal]
      _ = (pairCount n i j t : ℝ) := by simp [hcard]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_pairSet_left f h, sum_pairSet_right f h]
    at hsum
  have hm : ∑ p ∈ pairSet n i j t, boolToReal (f p.1) * boolToReal (f p.2) =
      (pairCount n i j t : ℝ) * pairCorr f i j t := by
    unfold pairCorr; field_simp [hpos.ne']
  rw [hm] at hsum
  nlinarith

/-- Diagonal identity: `pairCorr f i i i = layerAvg f i`. -/
theorem pairCorr_diag {n i : ℕ} (f : BooleanFun n) (hi : i ≤ n) :
    pairCorr f i i i = layerAvg (fun x => boolToReal (f x)) i := by
  have hvalid : ValidTriple n i i i := ⟨hi, hi, le_refl i, le_refl i, by omega⟩
  have hpos : (0 : ℝ) < (pairCount n i i i : ℝ) := by exact_mod_cast pairCount_pos hvalid
  have hdiag : ∀ p ∈ pairSet n i i i, p.1 = p.2 := by
    intro p hp
    simp only [pairSet, Finset.mem_filter, Finset.mem_product, hammingLayer] at hp
    have h1 : (supportOf p.1).card = i := hp.1.1.2
    have h2 : (supportOf p.2).card = i := hp.1.2.2
    have hinter : (supportOf p.1 ∩ supportOf p.2).card = i := hp.2
    have hsub1 : supportOf p.1 ∩ supportOf p.2 = supportOf p.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hsub2 : supportOf p.1 ∩ supportOf p.2 = supportOf p.2 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    have hsupp : supportOf p.1 = supportOf p.2 := hsub1.symm.trans hsub2
    have := congrArg indicator hsupp
    simpa [indicator_supportOf] using this
  have hsum : ∑ p ∈ pairSet n i i i, boolToReal (f p.1) * boolToReal (f p.2) =
      ∑ p ∈ pairSet n i i i, boolToReal (f p.1) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hdiag p hp]
    cases f p.2 <;> norm_num [boolToReal]
  unfold pairCorr
  rw [hsum, sum_pairSet_left f hvalid]
  field_simp [hpos.ne']

/-- Boundary identity at weight `0`: if `f 0 = false`, then `pairCorr f 0 j 0 = 0`. -/
theorem pairCorr_zero_left {n j : ℕ} (f : BooleanFun n) (hf0 : f (zeroVec n) = false) :
    pairCorr f 0 j 0 = 0 := by
  unfold pairCorr
  have hsum : ∑ p ∈ pairSet n 0 j 0, boolToReal (f p.1) * boolToReal (f p.2) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp only [pairSet, Finset.mem_filter, Finset.mem_product, hammingLayer] at hp
    have hsupp : supportOf p.1 = ∅ := Finset.card_eq_zero.mp hp.1.1.2
    have hx0 : p.1 = zeroVec n := by
      funext k
      have hk := congrFun (congrArg indicator hsupp) k
      simpa [indicator_supportOf, indicator, zeroVec] using hk
    rw [hx0, hf0]
    simp
  rw [hsum, zero_div]

private lemma eq_basisVec_of_mem_layer1 {n : ℕ} {x : Fin n → Bool} (hx : x ∈ hammingLayer n 1) :
    ∃ i : Fin n, x = basisVec i := by
  have hcard : (supportOf x).card = 1 := (Finset.mem_filter.mp hx).2
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  refine ⟨i, ?_⟩
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

/-- Boundary identity at weight `1` (`t = 1`): `pairCorr f 1 j 1 = layerAvg f j`. -/
theorem pairCorr_one_left_one {n j : ℕ} (f : BooleanFun n) (hj1 : 1 ≤ j) (hjn : j ≤ n)
    (hf1 : ∀ i : Fin n, f (basisVec i) = true) :
    pairCorr f 1 j 1 = layerAvg (fun x => boolToReal (f x)) j := by
  have hvalid : ValidTriple n 1 j 1 := ⟨by omega, hjn, le_refl 1, hj1, by omega⟩
  have hpos : (0 : ℝ) < (pairCount n 1 j 1 : ℝ) := by exact_mod_cast pairCount_pos hvalid
  have hsum : ∑ p ∈ pairSet n 1 j 1, boolToReal (f p.1) * boolToReal (f p.2) =
      ∑ p ∈ pairSet n 1 j 1, boolToReal (f p.2) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hx1 : p.1 ∈ hammingLayer n 1 := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    obtain ⟨i, hi⟩ := eq_basisVec_of_mem_layer1 hx1
    rw [hi, hf1 i]
    simp
  unfold pairCorr
  rw [hsum, sum_pairSet_right f hvalid]
  field_simp [hpos.ne']

/-- Boundary identity at weight `1` (`t = 0`): `pairCorr f 1 j 0 = layerAvg f j`. -/
theorem pairCorr_one_left_zero {n j : ℕ} (f : BooleanFun n) (hj : j + 1 ≤ n)
    (hf1 : ∀ i : Fin n, f (basisVec i) = true) :
    pairCorr f 1 j 0 = layerAvg (fun x => boolToReal (f x)) j := by
  have hvalid : ValidTriple n 1 j 0 := ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hpos : (0 : ℝ) < (pairCount n 1 j 0 : ℝ) := by exact_mod_cast pairCount_pos hvalid
  have hsum : ∑ p ∈ pairSet n 1 j 0, boolToReal (f p.1) * boolToReal (f p.2) =
      ∑ p ∈ pairSet n 1 j 0, boolToReal (f p.2) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hx1 : p.1 ∈ hammingLayer n 1 := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    obtain ⟨i, hi⟩ := eq_basisVec_of_mem_layer1 hx1
    rw [hi, hf1 i]
    simp
  unfold pairCorr
  rw [hsum, sum_pairSet_right f hvalid]
  field_simp [hpos.ne']

/-! ### Bivariate Symmetrisation Theorem (Binomial Basis Form) -/

/-- Helper count: for fixed `Y` (`|Y| = j`) and `S` with `|S ∩ Y| = r`, `|S \ Y| = s`,
the number of `x` with `|x ∩ Y| = a`, `|x \ Y| = b`, and `S ⊆ x` is
`(if r ≤ a then C(j - r, a - r) else 0) * (if s ≤ b then C(n - j - s, b - s) else 0)`. -/
private lemma card_bivar_filter_subset {n j a b : ℕ} (Y S : Finset (Fin n))
    (hY : Y.card = j) :
    ((hammingLayer n (a + b)).filter
      (fun x => (supportOf x ∩ Y).card = a ∧ S ⊆ supportOf x)).card =
      (if (S ∩ Y).card ≤ a then Nat.choose (j - (S ∩ Y).card) (a - (S ∩ Y).card) else 0) *
      (if (S \ Y).card ≤ b then Nat.choose (n - j - (S \ Y).card) (b - (S \ Y).card) else 0) := by
  classical
  set S1 := S ∩ Y
  set S2 := S \ Y
  have hYc : Yᶜ.card = n - j := by rw [Finset.card_compl, Fintype.card_fin, hY]
  have hS1sub : S1 ⊆ Y := Finset.inter_subset_right
  have hS2sub : S2 ⊆ Yᶜ := by
    intro k hk; exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hk).2
  by_cases h1 : S1.card ≤ a
  · by_cases h2 : S2.card ≤ b
    · simp only [h1, h2, ↓reduceIte]
      have hbij : ((hammingLayer n (a + b)).filter
          (fun x => (supportOf x ∩ Y).card = a ∧ S ⊆ supportOf x)).card =
          (Finset.powersetCard (a - S1.card) (Y \ S1) ×ˢ
           Finset.powersetCard (b - S2.card) (Yᶜ \ S2)).card := by
        apply Finset.card_bij (fun x _ => ((supportOf x ∩ Y) \ S1, (supportOf x \ Y) \ S2))
        · intro x hx
          obtain ⟨hxL, hxa, hSx⟩ := Finset.mem_filter.mp hx
          have hxCard : (supportOf x).card = a + b := (Finset.mem_filter.mp hxL).2
          have hS1x : S1 ⊆ supportOf x ∩ Y :=
            Finset.subset_inter (Finset.inter_subset_left.trans hSx) Finset.inter_subset_right
          have hS2x : S2 ⊆ supportOf x \ Y :=
            Finset.sdiff_subset_sdiff hSx (Finset.Subset.refl Y)
          have hxb : (supportOf x \ Y).card = b := by
            rw [Finset.card_sdiff, hxCard, Finset.inter_comm, hxa]; omega
          rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
          refine ⟨⟨Finset.sdiff_subset_sdiff Finset.inter_subset_right (Finset.Subset.refl S1), ?_⟩,
                  ⟨?_, ?_⟩⟩
          · rw [Finset.card_sdiff_of_subset hS1x, hxa]
          · intro k hk
            obtain ⟨hk1, hk2⟩ := Finset.mem_sdiff.mp hk
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (Finset.mem_sdiff.mp hk1).2, hk2⟩
          · rw [Finset.card_sdiff_of_subset hS2x, hxb]
        · intro x₁ hx₁ x₂ hx₂ hEq
          have hSx₁ : S ⊆ supportOf x₁ := (Finset.mem_filter.mp hx₁).2.2
          have hSx₂ : S ⊆ supportOf x₂ := (Finset.mem_filter.mp hx₂).2.2
          have hS1x₁ : S1 ⊆ supportOf x₁ ∩ Y :=
            Finset.subset_inter (Finset.inter_subset_left.trans hSx₁) Finset.inter_subset_right
          have hS1x₂ : S1 ⊆ supportOf x₂ ∩ Y :=
            Finset.subset_inter (Finset.inter_subset_left.trans hSx₂) Finset.inter_subset_right
          have hS2x₁ : S2 ⊆ supportOf x₁ \ Y :=
            Finset.sdiff_subset_sdiff hSx₁ (Finset.Subset.refl Y)
          have hS2x₂ : S2 ⊆ supportOf x₂ \ Y :=
            Finset.sdiff_subset_sdiff hSx₂ (Finset.Subset.refl Y)
          have hp1 : (supportOf x₁ ∩ Y) \ S1 = (supportOf x₂ ∩ Y) \ S1 := congrArg Prod.fst hEq
          have hp2 : (supportOf x₁ \ Y) \ S2 = (supportOf x₂ \ Y) \ S2 := congrArg Prod.snd hEq
          have heq1 : supportOf x₁ ∩ Y = supportOf x₂ ∩ Y := by
            rw [← Finset.union_sdiff_of_subset hS1x₁, ← Finset.union_sdiff_of_subset hS1x₂, hp1]
          have heq2 : supportOf x₁ \ Y = supportOf x₂ \ Y := by
            rw [← Finset.union_sdiff_of_subset hS2x₁, ← Finset.union_sdiff_of_subset hS2x₂, hp2]
          have hsupp : supportOf x₁ = supportOf x₂ := by
            rw [← finset_inter_union_sdiff (supportOf x₁) Y,
              ← finset_inter_union_sdiff (supportOf x₂) Y, heq1, heq2]
          have := congrArg indicator hsupp
          simpa [indicator_supportOf] using this
        · rintro ⟨U, V⟩ hUV
          rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard] at hUV
          obtain ⟨⟨hUsub, hUcard⟩, ⟨hVsub, hVcard⟩⟩ := hUV
          have hU_Y : U ⊆ Y := hUsub.trans Finset.sdiff_subset
          have hV_Yc : V ⊆ Yᶜ := hVsub.trans Finset.sdiff_subset
          have hS1U : Disjoint S1 U := by
            rw [Finset.disjoint_left]; intro k hkS1 hkU
            exact (Finset.mem_sdiff.mp (hUsub hkU)).2 hkS1
          have hS2V : Disjoint S2 V := by
            rw [Finset.disjoint_left]; intro k hkS2 hkV
            exact (Finset.mem_sdiff.mp (hVsub hkV)).2 hkS2
          let X1 := S1 ∪ U
          let X2 := S2 ∪ V
          have hX1_Y : X1 ⊆ Y := Finset.union_subset hS1sub hU_Y
          have hX2_Yc : X2 ⊆ Yᶜ := Finset.union_subset hS2sub hV_Yc
          have hX12 : Disjoint X1 X2 := by
            rw [Finset.disjoint_left]; intro k hk1 hk2
            exact (Finset.mem_compl.mp (hX2_Yc hk2)) (hX1_Y hk1)
          have hX1c : X1.card = a := by
            rw [Finset.card_union_of_disjoint hS1U, hUcard]; omega
          have hX2c : X2.card = b := by
            rw [Finset.card_union_of_disjoint hS2V, hVcard]; omega
          have hinterY : (X1 ∪ X2) ∩ Y = X1 := by
            have hdisjY : Disjoint X2 Y := by
              rw [Finset.disjoint_left]; intro k hk2 hkY
              exact (Finset.mem_compl.mp (hX2_Yc hk2)) hkY
            rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hX1_Y,
              Finset.disjoint_iff_inter_eq_empty.mp hdisjY, Finset.union_empty]
          have hsdiffY : (X1 ∪ X2) \ Y = X2 := by
            have hdisjY : Disjoint X2 Y := by
              rw [Finset.disjoint_left]; intro k hk2 hkY
              exact (Finset.mem_compl.mp (hX2_Yc hk2)) hkY
            rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_empty_iff_subset.mpr hX1_Y,
              Finset.empty_union, Finset.sdiff_eq_self_of_disjoint hdisjY]
          refine ⟨indicator (X1 ∪ X2), ?_, ?_⟩
          · rw [Finset.mem_filter, hammingLayer, Finset.mem_filter]
            refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_, ?_⟩
            · rw [supportOf_indicator, Finset.card_union_of_disjoint hX12, hX1c, hX2c]
            · rw [supportOf_indicator, hinterY, hX1c]
            · rw [supportOf_indicator, ← finset_inter_union_sdiff S Y]
              exact Finset.union_subset_union Finset.subset_union_left Finset.subset_union_left
          · simp only [supportOf_indicator, hinterY, hsdiffY, X1, X2,
              Finset.union_sdiff_cancel_left hS1U, Finset.union_sdiff_cancel_left hS2V]
      rw [hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
        Finset.card_sdiff_of_subset hS1sub, Finset.card_sdiff_of_subset hS2sub, hY, hYc]
    · simp only [h1, h2, ↓reduceIte, mul_zero]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx ⟨hxa, hSx⟩
      have hxCard : (supportOf x).card = a + b := (Finset.mem_filter.mp hx).2
      have hxb : (supportOf x \ Y).card = b := by
        rw [Finset.card_sdiff, hxCard, Finset.inter_comm, hxa]; omega
      have hS2x : S2 ⊆ supportOf x \ Y := Finset.sdiff_subset_sdiff hSx (Finset.Subset.refl Y)
      have := Finset.card_le_card hS2x
      omega
  · simp only [h1, ↓reduceIte, zero_mul]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx ⟨hxa, hSx⟩
    have hS1x : S1 ⊆ supportOf x ∩ Y :=
      Finset.subset_inter (Finset.inter_subset_left.trans hSx) Finset.inter_subset_right
    have := Finset.card_le_card hS1x
    omega

/-- **Bivariate Symmetrisation Theorem (Binomial Basis Form)**:
For any Boolean function `f : BooleanFun n` with `polyDegree f ≤ d` and any fixed layer `j ≤ n`,
there exist real coefficients `c : ℕ → ℕ → ℝ` such that for all `a ≤ j` and `b ≤ n - j`:

  `pairCorr f (a + b) j a = ∑ r ∈ range (d + 1), ∑ s ∈ range (d + 1 - r), c r s * C(a, r) * C(b, s)`. -/
theorem pairCorr_eq_bivar_binomial_sum {n d j : ℕ} (f : BooleanFun n)
    (hf : polyDegree f ≤ d) (hj : j ≤ n) :
    ∃ c : ℕ → ℕ → ℝ, ∀ a b : ℕ, a ≤ j → b ≤ n - j →
      pairCorr f (a + b) j a =
        ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
          c r s * (Nat.choose a r : ℝ) * (Nat.choose b s : ℝ) := by
  classical
  -- Define `c r s` directly from the Möbius coefficients of `f`.
  let μ : Finset (Fin n) → ℝ := fun S => (mobiusCoeff f S : ℝ)
  let c : ℕ → ℕ → ℝ := fun r s =>
    (∑ y ∈ hammingLayer n j, boolToReal (f y) *
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) =>
        (S ∩ supportOf y).card = r ∧ (S \ supportOf y).card = s), μ S) /
      ((Nat.choose n j : ℝ) * (Nat.choose j r : ℝ) * (Nat.choose (n - j) s : ℝ))
  refine ⟨c, fun a b ha hb => ?_⟩
  have hvalid : ValidTriple n (a + b) j a := ⟨by omega, hj, by omega, ha, by omega⟩
  have hpc_symm : pairCount n (a + b) j a = Nat.choose n j * Nat.choose j a * Nat.choose (n - j) b := by
    rw [pairCount_symm hvalid, pairCount]
    have : a + b - a = b := by omega
    rw [this]
  -- Expand the numerator of `pairCorr f (a + b) j a` by summing over `y ∈ hammingLayer n j` first.
  have hnum : ∑ p ∈ pairSet n (a + b) j a, boolToReal (f p.1) * boolToReal (f p.2) =
      ∑ y ∈ hammingLayer n j, boolToReal (f y) *
        ∑ S : Finset (Fin n), μ S *
          ((if (S ∩ supportOf y).card ≤ a then (Nat.choose (j - (S ∩ supportOf y).card) (a - (S ∩ supportOf y).card) : ℝ) else 0) *
           (if (S \ supportOf y).card ≤ b then (Nat.choose (n - j - (S \ supportOf y).card) (b - (S \ supportOf y).card) : ℝ) else 0)) := by
    have hswap : ∑ p ∈ pairSet n (a + b) j a, boolToReal (f p.1) * boolToReal (f p.2) =
        ∑ y ∈ hammingLayer n j, boolToReal (f y) *
          ∑ x ∈ (hammingLayer n (a + b)).filter (fun x => (supportOf x ∩ supportOf y).card = a),
            boolToReal (f x) := by
      rw [pairSet, Finset.sum_filter, Finset.sum_product_right]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum, ← Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _; ring
    rw [hswap]
    apply Finset.sum_congr rfl
    intro y hy
    congr 1
    have hyCard : (supportOf y).card = j := (Finset.mem_filter.mp hy).2
    have hrep : ∀ x : Fin n → Bool, boolToReal (f x) = ∑ S ∈ (supportOf x).powerset, μ S := by
      intro x
      have h := representsPoly_mobius f x
      change MvPolynomial.eval (fun i => boolToReal (x i)) (multilinearPoly μ) = boolToReal (f x) at h
      rw [eval_multilinearPoly] at h
      exact h.symm
    calc ∑ x ∈ (hammingLayer n (a + b)).filter (fun x => (supportOf x ∩ supportOf y).card = a),
          boolToReal (f x)
        = ∑ x ∈ (hammingLayer n (a + b)).filter (fun x => (supportOf x ∩ supportOf y).card = a),
            ∑ S : Finset (Fin n), if S ⊆ supportOf x then μ S else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hrep x, ← Finset.sum_filter]
          apply Finset.sum_congr _ (fun _ _ => rfl)
          ext S; simp [Finset.mem_powerset]
      _ = ∑ S : Finset (Fin n),
            ∑ x ∈ (hammingLayer n (a + b)).filter (fun x => (supportOf x ∩ supportOf y).card = a),
              if S ⊆ supportOf x then μ S else 0 := Finset.sum_comm
      _ = ∑ S : Finset (Fin n), μ S *
            ((((hammingLayer n (a + b)).filter
              (fun x => (supportOf x ∩ supportOf y).card = a ∧ S ⊆ supportOf x)).card) : ℝ) := by
          apply Finset.sum_congr rfl
          intro S _
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm, Finset.filter_filter]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro S _
          rw [card_bivar_filter_subset (supportOf y) S hyCard]
          congr 1
          push_cast
          split_ifs <;> simp
  -- Rewrite the `S`-sum grouped by `(r, s) = (|S ∩ y|, |S \ y|)` with `r + s ≤ d`.
  have hinner : ∀ y ∈ hammingLayer n j,
      (∑ S : Finset (Fin n), μ S *
        ((if (S ∩ supportOf y).card ≤ a then (Nat.choose (j - (S ∩ supportOf y).card) (a - (S ∩ supportOf y).card) : ℝ) else 0) *
         (if (S \ supportOf y).card ≤ b then (Nat.choose (n - j - (S \ supportOf y).card) (b - (S \ supportOf y).card) : ℝ) else 0))) /
      ((Nat.choose j a : ℝ) * (Nat.choose (n - j) b : ℝ)) =
      ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
        ((∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) =>
          (S ∩ supportOf y).card = r ∧ (S \ supportOf y).card = s), μ S) /
          ((Nat.choose j r : ℝ) * (Nat.choose (n - j) s : ℝ))) *
          (Nat.choose a r : ℝ) * (Nat.choose b s : ℝ) := by
    intro y hy
    have hyCard : (supportOf y).card = j := (Finset.mem_filter.mp hy).2
    let F : Finset (Fin n) → ℝ := fun S => μ S *
      ((if (S ∩ supportOf y).card ≤ a then (Nat.choose (j - (S ∩ supportOf y).card) (a - (S ∩ supportOf y).card) : ℝ) else 0) *
       (if (S \ supportOf y).card ≤ b then (Nat.choose (n - j - (S \ supportOf y).card) (b - (S \ supportOf y).card) : ℝ) else 0)) /
      ((Nat.choose j a : ℝ) * (Nat.choose (n - j) b : ℝ))
    rw [div_eq_mul_inv, Finset.sum_mul]
    simp_rw [← div_eq_mul_inv]
    change ∑ S : Finset (Fin n), F S = _
    -- Partition all `S : Finset (Fin n)` by `(r, s) = (|S ∩ y|, |S \ y|)`.
    let M := max n d + 1
    have hfib : ∑ S : Finset (Fin n), F S =
        ∑ p ∈ Finset.range M ×ˢ Finset.range M,
          ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) =>
            ((S ∩ supportOf y).card, (S \ supportOf y).card) = p), F S := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun S : Finset (Fin n) =>
        ((S ∩ supportOf y).card, (S \ supportOf y).card)) (t := Finset.range M ×ˢ Finset.range M)]
      intro S _
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      have h1 : (S ∩ supportOf y).card ≤ n := by simpa using Finset.card_le_univ (S ∩ supportOf y)
      have h2 : (S \ supportOf y).card ≤ n := by simpa using Finset.card_le_univ (S \ supportOf y)
      omega
    rw [hfib, Finset.sum_product]
    -- Restrict `r` to `range (d + 1)` and `s` to `range (d + 1 - r)` since `r + s > d → μ S = 0`.
    have hzero_gt : ∀ r s : ℕ, d < r + s →
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) =>
          ((S ∩ supportOf y).card, (S \ supportOf y).card) = (r, s)), F S = 0 := by
      intro r s hgt
      apply Finset.sum_eq_zero
      intro S hS
      have hp := (Finset.mem_filter.mp hS).2
      have hr : (S ∩ supportOf y).card = r := congrArg Prod.fst hp
      have hs : (S \ supportOf y).card = s := congrArg Prod.snd hp
      have hScard : S.card = r + s := by
        rw [← Finset.card_inter_add_card_sdiff S (supportOf y), hr, hs]
      have hmu0 : mobiusCoeff f S = 0 := mobiusCoeff_eq_zero_of_polyDegree_lt (by omega)
      simp [F, μ, hmu0]
    rw [← Finset.sum_subset (Finset.range_mono (by omega : d + 1 ≤ M))]
    · apply Finset.sum_congr rfl
      intro r hr
      have hrd : r ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      rw [← Finset.sum_subset (Finset.range_mono (by omega : d + 1 - r ≤ M))]
      · apply Finset.sum_congr rfl
        intro s hs
        have hsd : s < d + 1 - r := Finset.mem_range.mp hs
        -- Match the filter condition and apply `choose_sub_mul_choose` twice!
        have hfilt_eq : Finset.univ.filter (fun S : Finset (Fin n) =>
            ((S ∩ supportOf y).card, (S \ supportOf y).card) = (r, s)) =
            Finset.univ.filter (fun S : Finset (Fin n) =>
              (S ∩ supportOf y).card = r ∧ (S \ supportOf y).card = s) := by
          ext S; simp [Prod.ext_iff]
        rw [hfilt_eq]
        by_cases hrj : r ≤ j
        · by_cases hsnj : s ≤ n - j
          · have hja_pos : (Nat.choose j a : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos ha).ne'
            have hnb_pos : (Nat.choose (n - j) b : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hb).ne'
            have hjr_pos : (Nat.choose j r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hrj).ne'
            have hns_pos : (Nat.choose (n - j) s : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hsnj).ne'
            have hrat1 : (if r ≤ a then (Nat.choose (j - r) (a - r) : ℝ) else 0) / (Nat.choose j a : ℝ) =
                (Nat.choose a r : ℝ) / (Nat.choose j r : ℝ) := by
              rw [div_eq_div_iff hja_pos hjr_pos]
              have hid : ((if r ≤ a then Nat.choose (j - r) (a - r) else 0 : ℕ) : ℝ) *
                  (Nat.choose j r : ℝ) = (Nat.choose j a : ℝ) * (Nat.choose a r : ℝ) := by
                exact_mod_cast choose_sub_mul_choose (m := j) (k := a) (j := r) ha
              rw [mul_comm (Nat.choose a r : ℝ)]
              convert hid using 2
              split_ifs <;> simp
            have hrat2 : (if s ≤ b then (Nat.choose (n - j - s) (b - s) : ℝ) else 0) /
                (Nat.choose (n - j) b : ℝ) =
                (Nat.choose b s : ℝ) / (Nat.choose (n - j) s : ℝ) := by
              rw [div_eq_div_iff hnb_pos hns_pos]
              have hid : ((if s ≤ b then Nat.choose (n - j - s) (b - s) else 0 : ℕ) : ℝ) *
                  (Nat.choose (n - j) s : ℝ) = (Nat.choose (n - j) b : ℝ) * (Nat.choose b s : ℝ) := by
                exact_mod_cast choose_sub_mul_choose (m := n - j) (k := b) (j := s) hb
              rw [mul_comm (Nat.choose b s : ℝ)]
              convert hid using 2
              split_ifs <;> simp
            have hterm : ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin n) =>
                (S ∩ supportOf y).card = r ∧ (S \ supportOf y).card = s),
                F S = μ S * (((Nat.choose a r : ℝ) / (Nat.choose j r : ℝ)) *
                  ((Nat.choose b s : ℝ) / (Nat.choose (n - j) s : ℝ))) := by
              intro S hS
              obtain ⟨hSr, hSs⟩ := (Finset.mem_filter.mp hS).2
              dsimp only [F]
              rw [hSr, hSs, ← hrat1, ← hrat2]
              ring
            rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
            ring
          · -- `s > n - j`: `Nat.choose b s = 0` and no `S` has `|S \ y| = s`!
            have hbs0 : Nat.choose b s = 0 := Nat.choose_eq_zero_of_lt (by omega)
            have hemp : Finset.univ.filter (fun S : Finset (Fin n) =>
                (S ∩ supportOf y).card = r ∧ (S \ supportOf y).card = s) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro S _ ⟨_, hSs⟩
              have hle : (S \ supportOf y).card ≤ (supportOf y)ᶜ.card := by
                apply Finset.card_le_card
                intro k hk; exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hk).2
              rw [Finset.card_compl, Fintype.card_fin, hyCard] at hle
              omega
            simp [hemp, hbs0]
        · -- `r > j`: `Nat.choose a r = 0` and no `S` has `|S ∩ y| = r`!
          have har0 : Nat.choose a r = 0 := Nat.choose_eq_zero_of_lt (by omega)
          have hemp : Finset.univ.filter (fun S : Finset (Fin n) =>
              (S ∩ supportOf y).card = r ∧ (S \ supportOf y).card = s) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro S _ ⟨hSr, _⟩
            have hle : (S ∩ supportOf y).card ≤ (supportOf y).card :=
              Finset.card_le_card Finset.inter_subset_right
            omega
          simp [hemp, har0]
      · intro s _ hsnot
        exact hzero_gt r s (by rw [Finset.mem_range] at hsnot; omega)
    · intro r _ hrnot
      apply Finset.sum_eq_zero
      intro s _
      exact hzero_gt r s (by rw [Finset.mem_range] at hrnot; omega)
  -- Put everything together!
  unfold pairCorr
  rw [hnum, hpc_symm]
  push_cast
  have hdiv : ∀ (A B C : ℝ), A / (B * C) = (A / C) / B := fun A B C => by ring
  calc (∑ y ∈ hammingLayer n j, boolToReal (f y) *
          ∑ S : Finset (Fin n), μ S *
            ((if (S ∩ supportOf y).card ≤ a then (Nat.choose (j - (S ∩ supportOf y).card) (a - (S ∩ supportOf y).card) : ℝ) else 0) *
             (if (S \ supportOf y).card ≤ b then (Nat.choose (n - j - (S \ supportOf y).card) (b - (S \ supportOf y).card) : ℝ) else 0))) /
        ((Nat.choose n j : ℝ) * (Nat.choose j a : ℝ) * (Nat.choose (n - j) b : ℝ))
      = (∑ y ∈ hammingLayer n j, boolToReal (f y) *
          ((∑ S : Finset (Fin n), μ S *
            ((if (S ∩ supportOf y).card ≤ a then (Nat.choose (j - (S ∩ supportOf y).card) (a - (S ∩ supportOf y).card) : ℝ) else 0) *
             (if (S \ supportOf y).card ≤ b then (Nat.choose (n - j - (S \ supportOf y).card) (b - (S \ supportOf y).card) : ℝ) else 0))) /
           ((Nat.choose j a : ℝ) * (Nat.choose (n - j) b : ℝ)))) / (Nat.choose n j : ℝ) := by
        rw [mul_assoc (Nat.choose n j : ℝ), hdiv, div_eq_mul_inv (∑ y ∈ hammingLayer n j, _),
          Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        ring
    _ = (∑ y ∈ hammingLayer n j, boolToReal (f y) *
          ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
            ((∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) =>
              (S ∩ supportOf y).card = r ∧ (S \ supportOf y).card = s), μ S) /
              ((Nat.choose j r : ℝ) * (Nat.choose (n - j) s : ℝ))) *
              (Nat.choose a r : ℝ) * (Nat.choose b s : ℝ)) / (Nat.choose n j : ℝ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro y hy
        rw [hinner y hy]
    _ = ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1 - r),
          c r s * (Nat.choose a r : ℝ) * (Nat.choose b s : ℝ) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_comm (s := hammingLayer n j)]
        rw [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro s _
        dsimp only [c]
        have hpull : ∑ y ∈ hammingLayer n j,
            boolToReal (f y) *
              ((∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) =>
                (S ∩ supportOf y).card = r ∧ (S \ supportOf y).card = s), μ S) /
                ((Nat.choose j r : ℝ) * (Nat.choose (n - j) s : ℝ)) *
                (Nat.choose a r : ℝ) * (Nat.choose b s : ℝ)) =
            (∑ y ∈ hammingLayer n j, boolToReal (f y) *
              ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) =>
                (S ∩ supportOf y).card = r ∧ (S \ supportOf y).card = s), μ S) *
              ((Nat.choose a r : ℝ) * (Nat.choose b s : ℝ) /
                ((Nat.choose j r : ℝ) * (Nat.choose (n - j) s : ℝ))) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro y _; ring
        rw [hpull]
        ring

/-! ### Finite-Difference Annihilation and Layer-Product Identities -/

/-- The `m`-th forward difference of `u ↦ C(k + u, r)` vanishes whenever `r < m`. -/
theorem finDiff_choose_eq_zero :
    ∀ (m : ℕ) {r k : ℕ}, r < m →
      ∑ u ∈ Finset.range (m + 1),
        (-1 : ℤ) ^ (m - u) * (Nat.choose m u : ℤ) * (Nat.choose (k + u) r : ℤ) = 0 := by
  intro m
  induction m with
  | zero => intro r _ hr; omega
  | succ m ih =>
    intro r k hr
    -- Rewrite `Δ^{m+1} g(k) = ∑_{u=0}^m (-1)^{m-u} C(m, u) (g(k+u+1) - g(k+u))` via Pascal's rule.
    have hstep : ∀ g : ℕ → ℤ,
        ∑ u ∈ Finset.range (m + 2), (-1 : ℤ) ^ (m + 1 - u) * (Nat.choose (m + 1) u : ℤ) * g u =
        ∑ u ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - u) * (Nat.choose m u : ℤ) * (g (u + 1) - g u) := by
      intro g
      rw [Finset.sum_range_succ']
      simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
      have hsplit : ∑ u ∈ Finset.range (m + 1),
          (-1 : ℤ) ^ (m + 1 - (u + 1)) * (Nat.choose (m + 1) (u + 1) : ℤ) * g (u + 1) =
          ∑ u ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - u) * (Nat.choose m u : ℤ) * g (u + 1) +
          ∑ u ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - u) * (Nat.choose m (u + 1) : ℤ) * g (u + 1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro u _
        have hsub : m + 1 - (u + 1) = m - u := by omega
        rw [hsub, Nat.choose_succ_succ]
        push_cast
        ring
      rw [hsplit]
      have hshift : ∑ u ∈ Finset.range (m + 1),
          (-1 : ℤ) ^ (m - u) * (Nat.choose m (u + 1) : ℤ) * g (u + 1) + (-1 : ℤ) ^ (m + 1) * g 0 =
          -(∑ u ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - u) * (Nat.choose m u : ℤ) * g u) := by
        have hlast : ∑ u ∈ Finset.range (m + 1),
            (-1 : ℤ) ^ (m - u) * (Nat.choose m (u + 1) : ℤ) * g (u + 1) =
            ∑ u ∈ Finset.range m, (-1 : ℤ) ^ (m - u) * (Nat.choose m (u + 1) : ℤ) * g (u + 1) := by
          rw [Finset.sum_range_succ]
          simp
        rw [hlast, Finset.sum_range_succ']
        simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, neg_add_rev]
        have hneg : ∑ u ∈ Finset.range m,
            (-1 : ℤ) ^ (m - u) * (Nat.choose m (u + 1) : ℤ) * g (u + 1) =
            -(∑ u ∈ Finset.range m, (-1 : ℤ) ^ (m - (u + 1)) * (Nat.choose m (u + 1) : ℤ) * g (u + 1)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro u hu
          have hum : u < m := Finset.mem_range.mp hu
          have hexp : m - u = (m - (u + 1)) + 1 := by omega
          rw [hexp, pow_succ]
          ring
        rw [hneg, pow_succ]
        ring
      have hrhs : ∑ u ∈ Finset.range (m + 1),
          (-1 : ℤ) ^ (m - u) * (Nat.choose m u : ℤ) * (g (u + 1) - g u) =
          ∑ u ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - u) * (Nat.choose m u : ℤ) * g (u + 1) -
          ∑ u ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - u) * (Nat.choose m u : ℤ) * g u := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro u _; ring
      linarith
    rw [hstep (fun u => (Nat.choose (k + u) r : ℤ))]
    cases r with
    | zero =>
      simp
    | succ r' =>
      have hdiff : ∀ u, ((Nat.choose (k + (u + 1)) (r' + 1) : ℤ) - (Nat.choose (k + u) (r' + 1) : ℤ)) =
          (Nat.choose (k + u) r' : ℤ) := by
        intro u
        have hadd : k + (u + 1) = (k + u) + 1 := by omega
        rw [hadd, Nat.choose_succ_succ]
        push_cast
        ring
      simp_rw [hdiff]
      exact ih (by omega)

/-- Univariate `(d + 1)`-th finite difference of `layerAvg f` vanishes when `polyDegree f ≤ d`. -/
theorem layerAvg_finDiff_eq_zero {n d k : ℕ} (f : BooleanFun n) (hf : polyDegree f ≤ d)
    (hk : k + d + 1 ≤ n) :
    ∑ u ∈ Finset.range (d + 2),
      ((-1 : ℤ) ^ (d + 1 - u) * (Nat.choose (d + 1) u : ℤ) : ℝ) *
        layerAvg (fun x => boolToReal (f x)) (k + u) = 0 := by
  have hrep : ∀ x : Fin n → Bool,
      ∑ S ∈ (supportOf x).powerset, (mobiusCoeff f S : ℝ) = boolToReal (f x) := by
    intro x
    have h := representsPoly_mobius f x
    change MvPolynomial.eval (fun i => boolToReal (x i))
      (multilinearPoly (fun S => (mobiusCoeff f S : ℝ))) = boolToReal (f x) at h
    rwa [eval_multilinearPoly] at h
  have hdeg : ∀ S : Finset (Fin n), d < S.card → (mobiusCoeff f S : ℝ) = 0 := by
    intro S hS; simp [mobiusCoeff_eq_zero_of_polyDegree_lt (lt_of_le_of_lt hf hS)]
  obtain ⟨a, ha⟩ := layerAvg_eq_binomial_sum (fun x => boolToReal (f x))
    (fun S => (mobiusCoeff f S : ℝ)) hrep hdeg
  calc ∑ u ∈ Finset.range (d + 2),
        ((-1 : ℤ) ^ (d + 1 - u) * (Nat.choose (d + 1) u : ℤ) : ℝ) *
          layerAvg (fun x => boolToReal (f x)) (k + u)
      = ∑ u ∈ Finset.range (d + 2),
          ((-1 : ℤ) ^ (d + 1 - u) * (Nat.choose (d + 1) u : ℤ) : ℝ) *
            ∑ r ∈ Finset.range (d + 1), a r * (Nat.choose (k + u) r : ℝ) := by
        apply Finset.sum_congr rfl
        intro u hu
        have hku : k + u ≤ n := by have := Finset.mem_range.mp hu; omega
        rw [ha (k + u) hku]
    _ = ∑ r ∈ Finset.range (d + 1),
          a r * ∑ u ∈ Finset.range (d + 2),
            ((-1 : ℤ) ^ (d + 1 - u) * (Nat.choose (d + 1) u : ℤ) * (Nat.choose (k + u) r : ℤ) : ℝ) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro u _
        push_cast; ring
    _ = 0 := by
        apply Finset.sum_eq_zero
        intro r hr
        have h0 : ∑ u ∈ Finset.range (d + 2),
            (-1 : ℤ) ^ (d + 1 - u) * (Nat.choose (d + 1) u : ℤ) * (Nat.choose (k + u) r : ℤ) = 0 :=
          finDiff_choose_eq_zero (d + 1) (Finset.mem_range.mp hr)
        have h0R : ∑ u ∈ Finset.range (d + 2),
            ((-1 : ℤ) ^ (d + 1 - u) * (Nat.choose (d + 1) u : ℤ) * (Nat.choose (k + u) r : ℤ) : ℝ) = 0 := by
          exact_mod_cast h0
        rw [h0R, mul_zero]

/-- **Terwilliger Bivariate Finite-Difference Vanishing Identity**:
For `r + s = d + 1`, `a0 + r ≤ j`, `b0 + s ≤ n - j`, the `(r, s)` mixed finite difference of
`pairCorr f (a + b) j a` vanishes identically. -/
theorem pairCorr_bivarDiff_eq_zero {n d j r s a0 b0 : ℕ} (f : BooleanFun n)
    (hf : polyDegree f ≤ d) (hj : j ≤ n) (hrs : r + s = d + 1)
    (ha0 : a0 + r ≤ j) (hb0 : b0 + s ≤ n - j) :
    ∑ u ∈ Finset.range (r + 1), ∑ v ∈ Finset.range (s + 1),
      ((((-1 : ℤ) ^ (r - u) * (Nat.choose r u : ℤ)) *
        ((-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ)) : ℤ) : ℝ) *
        pairCorr f (a0 + u + b0 + v) j (a0 + u) = 0 := by
  obtain ⟨c, hc⟩ := pairCorr_eq_bivar_binomial_sum f hf hj
  have heval : ∀ u ∈ Finset.range (r + 1), ∀ v ∈ Finset.range (s + 1),
      pairCorr f (a0 + u + b0 + v) j (a0 + u) =
        ∑ p ∈ Finset.range (d + 1), ∑ q ∈ Finset.range (d + 1 - p),
          c p q * (Nat.choose (a0 + u) p : ℝ) * (Nat.choose (b0 + v) q : ℝ) := by
    intro u hu v hv
    have hu' : a0 + u ≤ j := by have := Finset.mem_range.mp hu; omega
    have hv' : b0 + v ≤ n - j := by have := Finset.mem_range.mp hv; omega
    have hadd : a0 + u + b0 + v = (a0 + u) + (b0 + v) := by omega
    rw [hadd, hc (a0 + u) (b0 + v) hu' hv']
  calc ∑ u ∈ Finset.range (r + 1), ∑ v ∈ Finset.range (s + 1),
        ((((-1 : ℤ) ^ (r - u) * (Nat.choose r u : ℤ)) *
          ((-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ)) : ℤ) : ℝ) *
          pairCorr f (a0 + u + b0 + v) j (a0 + u)
      = ∑ u ∈ Finset.range (r + 1), ∑ v ∈ Finset.range (s + 1),
          ∑ p ∈ Finset.range (d + 1), ∑ q ∈ Finset.range (d + 1 - p),
            c p q *
              ((((-1 : ℤ) ^ (r - u) * (Nat.choose r u : ℤ) * (Nat.choose (a0 + u) p : ℤ) : ℤ) : ℝ) *
               (((-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ) * (Nat.choose (b0 + v) q : ℤ) : ℤ) : ℝ)) := by
        apply Finset.sum_congr rfl; intro u hu
        apply Finset.sum_congr rfl; intro v hv
        rw [heval u hu v hv, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro p _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro q _
        push_cast; ring
    _ = ∑ p ∈ Finset.range (d + 1), ∑ q ∈ Finset.range (d + 1 - p),
          c p q *
            ((∑ u ∈ Finset.range (r + 1),
                (((-1 : ℤ) ^ (r - u) * (Nat.choose r u : ℤ) * (Nat.choose (a0 + u) p : ℤ) : ℤ) : ℝ)) *
             (∑ v ∈ Finset.range (s + 1),
                (((-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ) * (Nat.choose (b0 + v) q : ℤ) : ℤ) : ℝ))) := by
        -- Swap `(u, v)` past `(p, q)`.
        calc ∑ u ∈ Finset.range (r + 1), ∑ v ∈ Finset.range (s + 1),
              ∑ p ∈ Finset.range (d + 1), ∑ q ∈ Finset.range (d + 1 - p),
                c p q *
                  ((((-1 : ℤ) ^ (r - u) * (Nat.choose r u : ℤ) * (Nat.choose (a0 + u) p : ℤ) : ℤ) : ℝ) *
                   (((-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ) * (Nat.choose (b0 + v) q : ℤ) : ℤ) : ℝ))
            = ∑ u ∈ Finset.range (r + 1), ∑ p ∈ Finset.range (d + 1),
                ∑ v ∈ Finset.range (s + 1), ∑ q ∈ Finset.range (d + 1 - p),
                  c p q *
                    ((((-1 : ℤ) ^ (r - u) * (Nat.choose r u : ℤ) * (Nat.choose (a0 + u) p : ℤ) : ℤ) : ℝ) *
                     (((-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ) * (Nat.choose (b0 + v) q : ℤ) : ℤ) : ℝ)) := by
              apply Finset.sum_congr rfl; intro u _; exact Finset.sum_comm
          _ = ∑ p ∈ Finset.range (d + 1), ∑ u ∈ Finset.range (r + 1),
                ∑ q ∈ Finset.range (d + 1 - p), ∑ v ∈ Finset.range (s + 1),
                  c p q *
                    ((((-1 : ℤ) ^ (r - u) * (Nat.choose r u : ℤ) * (Nat.choose (a0 + u) p : ℤ) : ℤ) : ℝ) *
                     (((-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ) * (Nat.choose (b0 + v) q : ℤ) : ℤ) : ℝ)) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro p _
              apply Finset.sum_congr rfl; intro u _
              exact Finset.sum_comm
          _ = ∑ p ∈ Finset.range (d + 1), ∑ q ∈ Finset.range (d + 1 - p),
                ∑ u ∈ Finset.range (r + 1), ∑ v ∈ Finset.range (s + 1),
                  c p q *
                    ((((-1 : ℤ) ^ (r - u) * (Nat.choose r u : ℤ) * (Nat.choose (a0 + u) p : ℤ) : ℤ) : ℝ) *
                     (((-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ) * (Nat.choose (b0 + v) q : ℤ) : ℤ) : ℝ)) := by
              apply Finset.sum_congr rfl; intro p _; exact Finset.sum_comm
          _ = _ := by
              apply Finset.sum_congr rfl; intro p _
              apply Finset.sum_congr rfl; intro q _
              rw [Finset.sum_mul_sum, Finset.mul_sum]
              apply Finset.sum_congr rfl; intro u _
              rw [Finset.mul_sum]
    _ = 0 := by
        apply Finset.sum_eq_zero; intro p hp
        apply Finset.sum_eq_zero; intro q hq
        have hpq : p + q ≤ d := by
          have := Finset.mem_range.mp hp
          have := Finset.mem_range.mp hq
          omega
        by_cases hpr : p < r
        · have h0 : ∑ u ∈ Finset.range (r + 1),
              (-1 : ℤ) ^ (r - u) * (Nat.choose r u : ℤ) * (Nat.choose (a0 + u) p : ℤ) = 0 :=
            finDiff_choose_eq_zero r hpr
          have h0R : ∑ u ∈ Finset.range (r + 1),
              (((-1 : ℤ) ^ (r - u) * (Nat.choose r u : ℤ) * (Nat.choose (a0 + u) p : ℤ) : ℤ) : ℝ) = 0 := by
            exact_mod_cast h0
          rw [h0R, zero_mul, mul_zero]
        · have hqs : q < s := by omega
          have h0 : ∑ v ∈ Finset.range (s + 1),
              (-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ) * (Nat.choose (b0 + v) q : ℤ) = 0 :=
            finDiff_choose_eq_zero s hqs
          have h0R : ∑ v ∈ Finset.range (s + 1),
              (((-1 : ℤ) ^ (s - v) * (Nat.choose s v : ℤ) * (Nat.choose (b0 + v) q : ℤ) : ℤ) : ℝ) = 0 := by
            exact_mod_cast h0
          rw [h0R, mul_zero, mul_zero]

/-- **Layer-Product Identity**:
`∑_{t = i + j - n}^{min i j} C(i, t) C(n - i, j - t) * pairCorr f i j t = C(n, j) * p_i * p_j`. -/
theorem sum_pairCorr_layerProd {n i j : ℕ} (f : BooleanFun n) (hi : i ≤ n) (hj : j ≤ n) :
    ∑ t ∈ Finset.Icc (i + j - n) (min i j),
      (Nat.choose i t * Nat.choose (n - i) (j - t) : ℝ) * pairCorr f i j t =
      (Nat.choose n j : ℝ) *
        layerAvg (fun x => boolToReal (f x)) i *
        layerAvg (fun x => boolToReal (f x)) j := by
  classical
  have hci : (Nat.choose n i : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi).ne'
  have hcj : (Nat.choose n j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
  -- Multiply both sides by `C(n, i)`: both equal `∑_{x ∈ L_i, y ∈ L_j} f(x) f(y)`.
  have hlhs : (Nat.choose n i : ℝ) *
      ∑ t ∈ Finset.Icc (i + j - n) (min i j),
        (Nat.choose i t * Nat.choose (n - i) (j - t) : ℝ) * pairCorr f i j t =
      ∑ p ∈ hammingLayer n i ×ˢ hammingLayer n j, boolToReal (f p.1) * boolToReal (f p.2) := by
    rw [Finset.mul_sum]
    have hterm : ∀ t ∈ Finset.Icc (i + j - n) (min i j),
        (Nat.choose n i : ℝ) * ((Nat.choose i t * Nat.choose (n - i) (j - t) : ℝ) * pairCorr f i j t) =
          ∑ p ∈ pairSet n i j t, boolToReal (f p.1) * boolToReal (f p.2) := by
      intro t ht
      obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.mp ht
      have hvalid : ValidTriple n i j t :=
        ⟨hi, hj, ht2.trans (min_le_left i j), ht2.trans (min_le_right i j), by omega⟩
      have hpc : (pairCount n i j t : ℝ) ≠ 0 := by exact_mod_cast (pairCount_pos hvalid).ne'
      unfold pairCorr
      have hpc_eq : (pairCount n i j t : ℝ) =
          (Nat.choose n i : ℝ) * ((Nat.choose i t : ℝ) * (Nat.choose (n - i) (j - t) : ℝ)) := by
        unfold pairCount; push_cast; ring
      rw [← mul_assoc, ← hpc_eq]
      field_simp [hpc]
    rw [Finset.sum_congr rfl hterm]
    have hmaps : ∀ p ∈ hammingLayer n i ×ˢ hammingLayer n j,
        (supportOf p.1 ∩ supportOf p.2).card ∈ Finset.Icc (i + j - n) (min i j) := by
      intro p hp
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
      have hxi : (supportOf p.1).card = i := (Finset.mem_filter.mp hx).2
      have hyj : (supportOf p.2).card = j := (Finset.mem_filter.mp hy).2
      rw [Finset.mem_Icc]
      refine ⟨?_, le_min ?_ ?_⟩
      · have hu : (supportOf p.1 ∪ supportOf p.2).card ≤ n := by
          simpa using Finset.card_le_univ (supportOf p.1 ∪ supportOf p.2)
        have hinc := Finset.card_union_add_card_inter (supportOf p.1) (supportOf p.2)
        omega
      · rw [← hxi]; exact Finset.card_le_card Finset.inter_subset_left
      · rw [← hyj]; exact Finset.card_le_card Finset.inter_subset_right
    exact Finset.sum_fiberwise_of_maps_to hmaps _
  have hrhs : (Nat.choose n i : ℝ) *
      ((Nat.choose n j : ℝ) *
        layerAvg (fun x => boolToReal (f x)) i *
        layerAvg (fun x => boolToReal (f x)) j) =
      ∑ p ∈ hammingLayer n i ×ˢ hammingLayer n j, boolToReal (f p.1) * boolToReal (f p.2) := by
    rw [layerAvg, layerAvg]
    have hmul : (Nat.choose n i : ℝ) *
        ((Nat.choose n j : ℝ) * (realLayerSum (fun x => boolToReal (f x)) i / (Nat.choose n i : ℝ)) *
          (realLayerSum (fun x => boolToReal (f x)) j / (Nat.choose n j : ℝ))) =
        realLayerSum (fun x => boolToReal (f x)) i * realLayerSum (fun x => boolToReal (f x)) j := by
      field_simp [hci, hcj]
    rw [hmul, realLayerSum, realLayerSum, Finset.sum_product, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
  exact mul_left_cancel₀ hci (hlhs.trans hrhs.symm)

end DegreeSensitivity
