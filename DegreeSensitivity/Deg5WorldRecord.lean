module

public import DegreeSensitivity.Deg5CertData
public import DegreeSensitivity.Deg5Graph
public import DegreeSensitivity.RigidityMoments

@[expose] public section

/-!
# New World Record: `B_5 ≤ 14` (Impossibility of `(n = 15, d = 5)`)

Complete, zero-`sorry`, zero-`native_decide` proof that every Boolean function of polynomial
degree `≤ 5` has maximum sensitivity `≤ 14` (strictly beating Wellens's 2022 record `B_5 ≤ 15`).

Uses the 4 kernel-verified pure-integer Terwilliger LP certificates in `Deg5CertData`, the
polymorphic weight-3/4 moment & link-graph rigidity lemmas in `RigidityMoments`, and the
5-regular triangle-free induced-`2K₂`-free graph impossibility in `Deg5Graph`.
-/

namespace DegreeSensitivity

open scoped BigOperators

/-! ### Step 1: Unique Degree-5 Layer Profile `S7` -/

private lemma deg5_diff6 (f : BooleanFun 15) (hf : polyDegree f ≤ 5) (k : ℕ) (hk : k + 6 ≤ 15) :
    layerAvg (fun x => boolToReal (f x)) k -
    6 * layerAvg (fun x => boolToReal (f x)) (k + 1) +
    15 * layerAvg (fun x => boolToReal (f x)) (k + 2) -
    20 * layerAvg (fun x => boolToReal (f x)) (k + 3) +
    15 * layerAvg (fun x => boolToReal (f x)) (k + 4) -
    6 * layerAvg (fun x => boolToReal (f x)) (k + 5) +
    layerAvg (fun x => boolToReal (f x)) (k + 6) = 0 := by
  have h := layerAvg_finDiff_eq_zero f hf hk
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at h
  have hc0 : Nat.choose 6 0 = 1 := by decide
  have hc1 : Nat.choose 6 1 = 6 := by decide
  have hc2 : Nat.choose 6 2 = 15 := by decide
  have hc3 : Nat.choose 6 3 = 20 := by decide
  have hc4 : Nat.choose 6 4 = 15 := by decide
  have hc5 : Nat.choose 6 5 = 6 := by decide
  have hc6 : Nat.choose 6 6 = 1 := by decide
  rw [hc0, hc1, hc2, hc3, hc4, hc5, hc6] at h
  norm_num at h
  linarith

private lemma deg5_step1_profile (f : BooleanFun 15) (hf : polyDegree f ≤ 5)
    (hf0 : f (zeroVec 15) = false) (hf1 : ∀ i : Fin 15, f (basisVec i) = true) :
    (∀ q ∈ deg5S7LayerSums15, realLayerSum (fun x => boolToReal (f x)) q.1 = (q.2 : ℝ)) ∧
    layerAvg (fun x => boolToReal (f x)) 2 = 1 ∧
    layerAvg (fun x => boolToReal (f x)) 13 = 0 ∧
    layerAvg (fun x => boolToReal (f x)) 14 = 0 := by
  set p : ℕ → ℝ := fun k => layerAvg (fun x => boolToReal (f x)) k
  have hstep1 := terw_lp_bound f hf hf0 hf1 [] (by simp) [] (by simp) deg5Step1_tree
    [(2, 1), (13, -1), (14, -1), (15, 1)] [] deg5Step1_scale deg5Step1_lb deg5Step1_cert_ok
  simp only [evalTargetP, evalTargetM, add_zero] at hstep1
  have hsc_pos : (0 : ℝ) < (deg5Step1_scale : ℝ) := by
    have : 0 < deg5Step1_scale := by decide
    exact_mod_cast this
  have hlb_eq : (deg5Step1_lb : ℝ) = 2 * (deg5Step1_scale : ℝ) := by
    have : deg5Step1_lb = 2 * (deg5Step1_scale : ℤ) := by decide
    exact_mod_cast this
  have hineq : 2 ≤ p 2 - p 13 - p 14 + p 15 := by
    rw [hlb_eq] at hstep1; push_cast at hstep1; dsimp only [p]; nlinarith
  have hp0 : p 0 = 0 := layerAvg_bool_zero hf0
  have hp1 : p 1 = 1 := layerAvg_bool_one (by omega) hf1
  have hp2_le : p 2 ≤ 1 := layerAvg_bool_le_one f 2 (by omega)
  have hp13_ge : 0 ≤ p 13 := layerAvg_bool_nonneg f 13
  have hp14_ge : 0 ≤ p 14 := layerAvg_bool_nonneg f 14
  have hp15_le : p 15 ≤ 1 := layerAvg_bool_le_one f 15 (by omega)
  have hp2 : p 2 = 1 := by linarith
  have hp13 : p 13 = 0 := by linarith
  have hp14 : p 14 = 0 := by linarith
  have hp15 : p 15 = 1 := by linarith
  have hd0 := deg5_diff6 f hf 0 (by omega)
  have hd1 := deg5_diff6 f hf 1 (by omega)
  have hd2 := deg5_diff6 f hf 2 (by omega)
  have hd3 := deg5_diff6 f hf 3 (by omega)
  have hd4 := deg5_diff6 f hf 4 (by omega)
  have hd5 := deg5_diff6 f hf 5 (by omega)
  have hd6 := deg5_diff6 f hf 6 (by omega)
  have hd7 := deg5_diff6 f hf 7 (by omega)
  have hd8 := deg5_diff6 f hf 8 (by omega)
  have hd9 := deg5_diff6 f hf 9 (by omega)
  change p 0 - 6 * p 1 + 15 * p 2 - 20 * p 3 + 15 * p 4 - 6 * p 5 + p 6 = 0 at hd0
  change p 1 - 6 * p 2 + 15 * p 3 - 20 * p 4 + 15 * p 5 - 6 * p 6 + p 7 = 0 at hd1
  change p 2 - 6 * p 3 + 15 * p 4 - 20 * p 5 + 15 * p 6 - 6 * p 7 + p 8 = 0 at hd2
  change p 3 - 6 * p 4 + 15 * p 5 - 20 * p 6 + 15 * p 7 - 6 * p 8 + p 9 = 0 at hd3
  change p 4 - 6 * p 5 + 15 * p 6 - 20 * p 7 + 15 * p 8 - 6 * p 9 + p 10 = 0 at hd4
  change p 5 - 6 * p 6 + 15 * p 7 - 20 * p 8 + 15 * p 9 - 6 * p 10 + p 11 = 0 at hd5
  change p 6 - 6 * p 7 + 15 * p 8 - 20 * p 9 + 15 * p 10 - 6 * p 11 + p 12 = 0 at hd6
  change p 7 - 6 * p 8 + 15 * p 9 - 20 * p 10 + 15 * p 11 - 6 * p 12 + p 13 = 0 at hd7
  change p 8 - 6 * p 9 + 15 * p 10 - 20 * p 11 + 15 * p 12 - 6 * p 13 + p 14 = 0 at hd8
  change p 9 - 6 * p 10 + 15 * p 11 - 20 * p 12 + 15 * p 13 - 6 * p 14 + p 15 = 0 at hd9
  have hp3 : p 3 = 8 / 13 := by linarith
  have hp4 : p 4 = 3 / 13 := by linarith
  have hp5 : p 5 = 6 / 143 := by linarith
  have hp6 : p 6 = 14 / 143 := by linarith
  have hp7 : p 7 = 49 / 143 := by linarith
  have hp8 : p 8 = 94 / 143 := by linarith
  have hp9 : p 9 = 129 / 143 := by linarith
  have hp10 : p 10 = 137 / 143 := by linarith
  have hp11 : p 11 = 10 / 13 := by linarith
  have hp12 : p 12 = 5 / 13 := by linarith
  have hfromAvg : ∀ (k s : ℕ), k ≤ 15 → (Nat.choose 15 k : ℝ) * p k = (s : ℝ) →
      realLayerSum (fun x => boolToReal (f x)) k = (s : ℝ) := by
    intro k s hk hmul
    have hc : (Nat.choose 15 k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
    have : realLayerSum (fun x => boolToReal (f x)) k = (Nat.choose 15 k : ℝ) * p k := by
      simp only [p, layerAvg]; field_simp [hc]
    rw [this, hmul]
  refine ⟨?_, hp2, hp13, hp14⟩
  intro q hq
  simp only [deg5S7LayerSums15, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
  · exact hfromAvg 0 0 (by omega) (by rw [hp0]; norm_num)
  · exact hfromAvg 1 15 (by omega) (by rw [hp1]; norm_num)
  · exact hfromAvg 2 105 (by omega) (by rw [hp2, (by decide : Nat.choose 15 2 = 105)]; norm_num)
  · exact hfromAvg 3 280 (by omega) (by rw [hp3, (by decide : Nat.choose 15 3 = 455)]; norm_num)
  · exact hfromAvg 4 315 (by omega) (by rw [hp4, (by decide : Nat.choose 15 4 = 1365)]; norm_num)
  · exact hfromAvg 5 126 (by omega) (by rw [hp5, (by decide : Nat.choose 15 5 = 3003)]; norm_num)
  · exact hfromAvg 6 490 (by omega) (by rw [hp6, (by decide : Nat.choose 15 6 = 5005)]; norm_num)
  · exact hfromAvg 7 2205 (by omega) (by rw [hp7, (by decide : Nat.choose 15 7 = 6435)]; norm_num)
  · exact hfromAvg 8 4230 (by omega) (by rw [hp8, (by decide : Nat.choose 15 8 = 6435)]; norm_num)
  · exact hfromAvg 9 4515 (by omega) (by rw [hp9, (by decide : Nat.choose 15 9 = 5005)]; norm_num)
  · exact hfromAvg 10 2877 (by omega) (by rw [hp10, (by decide : Nat.choose 15 10 = 3003)]; norm_num)
  · exact hfromAvg 11 1050 (by omega) (by rw [hp11, (by decide : Nat.choose 15 11 = 1365)]; norm_num)
  · exact hfromAvg 12 175 (by omega) (by rw [hp12, (by decide : Nat.choose 15 12 = 455)]; norm_num)
  · exact hfromAvg 13 0 (by omega) (by rw [hp13]; norm_num)
  · exact hfromAvg 14 0 (by omega) (by rw [hp14]; norm_num)
  · exact hfromAvg 15 1 (by omega) (by rw [hp15]; norm_num)

/-! ### Step 2: Coordinate Restriction `D^(3)(i) = 56` and Quadratic Equation -/

private lemma deg5_step2_quadEq (f : BooleanFun 15) (hf : polyDegree f ≤ 5)
    (hf0 : f (zeroVec 15) = false) (hf1 : ∀ i : Fin 15, f (basisVec i) = true)
    (hp2 : layerAvg (fun x => boolToReal (f x)) 2 = 1)
    (hS3 : realLayerSum (fun x => boolToReal (f x)) 3 = 280)
    (hp13 : layerAvg (fun x => boolToReal (f x)) 13 = 0)
    (hp14 : layerAvg (fun x => boolToReal (f x)) 14 = 0) :
    858 * pairCorr f 3 3 1 + 312 * pairCorr f 3 3 2 + 13 * pairCorr f 3 3 3 = 448 := by
  have hL2 : ∀ x ∈ hammingLayer 15 2, f x = true := eq_true_of_layerAvg_eq_one f (by omega) hp2
  have hL13 : ∀ x ∈ hammingLayer 15 13, f x = false := eq_false_of_layerAvg_eq_zero f (by omega) hp13
  have hL14 : ∀ x ∈ hammingLayer 15 14, f x = false := eq_false_of_layerAvg_eq_zero f (by omega) hp14
  have hD3 : ∀ i : Fin 15, coordDeg3 f i = 56 := by
    intro i
    let g : BooleanFun 14 := restrictFalse f i
    have hg_deg : polyDegree g ≤ 5 := (polyDegree_restrictFalse_le f i).trans hf
    have hg0 : g (zeroVec 14) = false := by simp [g, restrictFalse, insertNth_false_zeroVec, hf0]
    have hg1 : ∀ j : Fin 14, g (basisVec j) = true := by
      intro j; simp [g, restrictFalse, insertNth_false_basisVec, hf1]
    have hglayers : ∀ q ∈ deg5LayerSums14, realLayerSum (fun y => boolToReal (g y)) q.1 = (q.2 : ℝ) := by
      intro q hq
      simp only [deg5LayerSums14, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · dsimp only; unfold realLayerSum
        calc ∑ y ∈ hammingLayer 14 2, boolToReal (g y)
            = ∑ _y ∈ hammingLayer 14 2, (1 : ℝ) := by
              apply Finset.sum_congr rfl; intro y hy
              have hy15 : i.insertNth false y ∈ hammingLayer 15 2 := by
                rw [mem_hammingLayer_iff] at hy ⊢; rw [card_supportOf_insertNth_false, hy]
              simp [g, restrictFalse, hL2 _ hy15]
          _ = ((hammingLayer 14 2).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          _ = 91 := by rw [card_hammingLayer, (by decide : Nat.choose 14 2 = 91)]; norm_num
      · dsimp only; unfold realLayerSum
        calc ∑ y ∈ hammingLayer 14 13, boolToReal (g y)
            = ∑ _y ∈ hammingLayer 14 13, (0 : ℝ) := by
              apply Finset.sum_congr rfl; intro y hy
              have hy15 : i.insertNth false y ∈ hammingLayer 15 13 := by
                rw [mem_hammingLayer_iff] at hy ⊢; rw [card_supportOf_insertNth_false, hy]
              simp [g, restrictFalse, hL13 _ hy15]
          _ = 0 := Finset.sum_const_zero
          _ = ((0 : ℕ) : ℝ) := Nat.cast_zero.symm
      · dsimp only; unfold realLayerSum
        calc ∑ y ∈ hammingLayer 14 14, boolToReal (g y)
            = ∑ _y ∈ hammingLayer 14 14, (0 : ℝ) := by
              apply Finset.sum_congr rfl; intro y hy
              have hy15 : i.insertNth false y ∈ hammingLayer 15 14 := by
                rw [mem_hammingLayer_iff] at hy ⊢; rw [card_supportOf_insertNth_false, hy]
              simp [g, restrictFalse, hL14 _ hy15]
          _ = 0 := Finset.sum_const_zero
          _ = ((0 : ℕ) : ℝ) := Nat.cast_zero.symm
    have h2a := terw_lp_bound g hg_deg hg0 hg1 deg5LayerSums14 hglayers [] (by simp)
      deg5Step2a_tree [(3, 1)] [] deg5Step2a_scale deg5Step2a_lb deg5Step2a_cert_ok
    have h2b := terw_lp_bound g hg_deg hg0 hg1 deg5LayerSums14 hglayers [] (by simp)
      deg5Step2b_tree [(3, -1)] [] deg5Step2b_scale deg5Step2b_lb deg5Step2b_cert_ok
    simp only [evalTargetP, evalTargetM, add_zero] at h2a h2b
    have h2a_pos : (0 : ℝ) < (deg5Step2a_scale : ℝ) := by
      have : 0 < deg5Step2a_scale := by decide
      exact_mod_cast this
    have h2a_eq : 13 * (deg5Step2a_lb : ℝ) = 8 * (deg5Step2a_scale : ℝ) := by
      have : 13 * deg5Step2a_lb = 8 * (deg5Step2a_scale : ℤ) := by decide
      exact_mod_cast this
    have h2b_pos : (0 : ℝ) < (deg5Step2b_scale : ℝ) := by
      have : 0 < deg5Step2b_scale := by decide
      exact_mod_cast this
    have h2b_eq : 13 * (deg5Step2b_lb : ℝ) = -(8 * (deg5Step2b_scale : ℝ)) := by
      have : 13 * deg5Step2b_lb = -(8 * (deg5Step2b_scale : ℤ)) := by decide
      exact_mod_cast this
    have hg_p3 : layerAvg (fun y => boolToReal (g y)) 3 = 8 / 13 := by
      push_cast at h2a h2b; nlinarith
    have hg_S3 : realLayerSum (fun y => boolToReal (g y)) 3 = 224 := by
      have hc : (Nat.choose 14 3 : ℝ) = 364 := by
        rw [(by decide : Nat.choose 14 3 = 364)]; norm_num
      have havg : realLayerSum (fun y => boolToReal (g y)) 3 / (364 : ℝ) = 8 / 13 := by
        rw [layerAvg, hc] at hg_p3; exact hg_p3
      linarith
    have hsplit := coordDeg3_add_restrictFalse f i
    change coordDeg3 f i + realLayerSum (fun y => boolToReal (g y)) 3 =
      realLayerSum (fun x => boolToReal (f x)) 3 at hsplit
    linarith
  have hsq := sum_coordDeg3_sq (n := 15) (by omega) f
  have hlhs : ∑ i : Fin 15, (coordDeg3 f i) ^ 2 = 47040 := by
    calc ∑ i : Fin 15, (coordDeg3 f i) ^ 2 = ∑ _i : Fin 15, (56 : ℝ) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => by rw [hD3 i])
      _ = 47040 := by simp; norm_num
  rw [hlhs] at hsq
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at hsq
  have hc1 : pairCount 15 3 3 1 = 90090 := by decide
  have hc2 : pairCount 15 3 3 2 = 16380 := by decide
  have hc3 : pairCount 15 3 3 3 = 455 := by decide
  rw [hc1, hc2, hc3] at hsq
  norm_num at hsq
  linarith

/-! ### Step 3 & Step 4: SOS Rigidity → Link Graph → Contradiction (`B_5 ≤ 14`) -/

/-- **Core Impossibility Theorem**: No normalized `(n = 15, d = 5)` Boolean function exists. -/
theorem no_normalized_deg5_dim15 :
    ¬ ∃ f : BooleanFun 15, polyDegree f ≤ 5 ∧
      f (zeroVec 15) = false ∧ ∀ i : Fin 15, f (basisVec i) = true := by
  rintro ⟨f, hf, hf0, hf1⟩
  obtain ⟨hlayers, hp2, hp13, hp14⟩ := deg5_step1_profile f hf hf0 hf1
  have hS3 : realLayerSum (fun x => boolToReal (f x)) 3 = 280 := by
    have := hlayers (3, 280) (by decide); simpa using this
  have hS4 : realLayerSum (fun x => boolToReal (f x)) 4 = 315 := by
    have := hlayers (4, 315) (by decide); simpa using this
  have hquad := deg5_step2_quadEq f hf hf0 hf1 hp2 hS3 hp13 hp14
  have hcustom : ∀ eq ∈ deg5CustomEqs15,
      (∀ q ∈ eq.1, ValidTriple 15 q.1 q.2.1 q.2.2.1) ∧ evalTargetM f eq.1 = (eq.2 : ℝ) := by
    intro eq heq
    simp only [deg5CustomEqs15, List.mem_singleton] at heq
    subst heq
    refine ⟨?_, ?_⟩
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;>
        exact ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega⟩
    · simp only [evalTargetM]; push_cast; linarith
  have h3 := terw_lp_bound f hf hf0 hf1 deg5S7LayerSums15 hlayers deg5CustomEqs15 hcustom
    deg5Step3_tree [] [(3, 4, 3, 1), (3, 3, 2, -1)] deg5Step3_scale deg5Step3_lb deg5Step3_cert_ok
  simp only [evalTargetP, evalTargetM, zero_add] at h3
  have hsc_pos : (0 : ℝ) < (deg5Step3_scale : ℝ) := by
    have : 0 < deg5Step3_scale := by decide
    exact_mod_cast this
  have hlb_eq : 39 * (deg5Step3_lb : ℝ) = -(5 * (deg5Step3_scale : ℝ)) := by
    have : 39 * deg5Step3_lb = -(5 * (deg5Step3_scale : ℤ)) := by decide
    exact_mod_cast this
  have hlp : pairCorr f 3 3 2 - pairCorr f 3 4 3 - 5 / 39 ≤ 0 := by
    push_cast at h3; nlinarith
  -- Evaluate the two SOS sums via the polymorphic moment theorems from `RigidityMoments`!
  set Pairs := Finset.powersetCard 2 (Finset.univ : Finset (Fin 15))
  set Quads := Finset.powersetCard 4 (Finset.univ : Finset (Fin 15))
  have hcardP : Pairs.card = 105 := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]; decide
  have hcardQ : Quads.card = 1365 := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]; decide
  have hpc332 : pairCount 15 3 3 2 = 16380 := by decide
  have hpc343 : pairCount 15 3 4 3 = 5460 := by decide
  have hpair_eq : ∑ P ∈ Pairs, (pairDeg3 f P - 8) ^ 2 = 16380 * pairCorr f 3 3 2 - 5880 := by
    have hm1 := sum_pairDeg3 f
    have hm2 := sum_pairDeg3_sq (n := 15) (by omega) f
    rw [hS3] at hm1 hm2; rw [hpc332] at hm2
    calc ∑ P ∈ Pairs, (pairDeg3 f P - 8) ^ 2
        = ∑ P ∈ Pairs, ((pairDeg3 f P) ^ 2 - 16 * pairDeg3 f P + 64) :=
          Finset.sum_congr rfl (fun _ _ => by ring)
      _ = (∑ P ∈ Pairs, (pairDeg3 f P) ^ 2) - 16 * (∑ P ∈ Pairs, pairDeg3 f P) +
            ∑ _P ∈ Pairs, (64 : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 16380 * pairCorr f 3 3 2 - 5880 := by
          rw [hm2, hm1, Finset.sum_const, nsmul_eq_mul, hcardP]; norm_num; ring
  have hquad_eq : ∑ Q ∈ Quads, (2 * boolToReal (f (indicator Q)) - quadDeg3 f Q + 2) ^ 2 =
      16380 * pairCorr f 3 3 2 - 21840 * pairCorr f 3 4 3 - 840 := by
    have hmf := sum_quad_f f
    have hmf2 : ∑ Q ∈ Quads, (boolToReal (f (indicator Q))) ^ 2 = 315 := by
      calc ∑ Q ∈ Quads, (boolToReal (f (indicator Q))) ^ 2
          = ∑ Q ∈ Quads, boolToReal (f (indicator Q)) :=
            Finset.sum_congr rfl (fun Q _ => by cases f (indicator Q) <;> norm_num [boolToReal])
        _ = 315 := by rw [hmf, hS4]
    have hmt := sum_quadDeg3 f
    have hmft := sum_quad_f_mul_quadDeg3 (n := 15) (by omega) f
    have hmt2 := sum_quadDeg3_sq (n := 15) (by omega) f
    rw [hS4] at hmf; rw [hS3] at hmt hmt2; rw [hpc343] at hmft; rw [hpc332] at hmt2
    calc ∑ Q ∈ Quads, (2 * boolToReal (f (indicator Q)) - quadDeg3 f Q + 2) ^ 2
        = ∑ Q ∈ Quads, (4 * (boolToReal (f (indicator Q))) ^ 2 + (quadDeg3 f Q) ^ 2 + 4 -
            4 * (boolToReal (f (indicator Q)) * quadDeg3 f Q) +
            8 * boolToReal (f (indicator Q)) - 4 * quadDeg3 f Q) :=
          Finset.sum_congr rfl (fun _ _ => by ring)
      _ = 4 * (∑ Q ∈ Quads, (boolToReal (f (indicator Q))) ^ 2) +
          (∑ Q ∈ Quads, (quadDeg3 f Q) ^ 2) + (∑ _Q ∈ Quads, (4 : ℝ)) -
          4 * (∑ Q ∈ Quads, boolToReal (f (indicator Q)) * quadDeg3 f Q) +
          8 * (∑ Q ∈ Quads, boolToReal (f (indicator Q))) -
          4 * (∑ Q ∈ Quads, quadDeg3 f Q) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 16380 * pairCorr f 3 3 2 - 21840 * pairCorr f 3 4 3 - 840 := by
          rw [hmf2, hmt2, hmft, hmf, hmt, Finset.sum_const, nsmul_eq_mul, hcardQ]; norm_num; ring
  have hpair_nn : 0 ≤ ∑ P ∈ Pairs, (pairDeg3 f P - 8) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hquad_nn : 0 ≤ ∑ Q ∈ Quads, (2 * boolToReal (f (indicator Q)) - quadDeg3 f Q + 2) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpair_zero : ∑ P ∈ Pairs, (pairDeg3 f P - 8) ^ 2 = 0 := by linarith
  have hquad_zero : ∑ Q ∈ Quads, (2 * boolToReal (f (indicator Q)) - quadDeg3 f Q + 2) ^ 2 = 0 := by
    linarith
  have hpair8 : ∀ P ∈ Pairs, pairDeg3 f P = ((8 : ℕ) : ℝ) := by
    intro P hP
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hpair_zero P hP
    have hsq := sq_eq_zero_iff.mp h0
    norm_num; linarith
  have hquad_rig : ∀ Q ∈ Quads, quadDeg3 f Q = 2 + 2 * boolToReal (f (indicator Q)) := by
    intro Q hQ
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hquad_zero Q hQ
    have hsq := sq_eq_zero_iff.mp h0
    linarith
  obtain ⟨adj, hirrefl, hsymm, hreg, htrifree, h2k2free⟩ :=
    exists_reg_trifree_2k2free_of_rigidity (m := 14) (d0 := 8) (r := 5) (by omega) f hpair8 hquad_rig
  exact no_5reg_trifree_2k2free_14 adj hirrefl hsymm hreg htrifree h2k2free

/-- **World Record `B_5 ≤ 14`**: Every Boolean function of polynomial degree `≤ 5` has maximum
sensitivity `≤ 14` (beating Wellens 2022 `B_5 ≤ 15`). -/
theorem maxSensitivity_le_fourteen_of_deg_le_five_proof {m : ℕ} (f : BooleanFun m)
    (hf : polyDegree f ≤ 5) : maxSensitivity f ≤ 14 := by
  have hlt := maxSensitivity_lt_of_no_normalized (k := 15) (d := 5) no_normalized_deg5_dim15 m f hf
  omega

end DegreeSensitivity
