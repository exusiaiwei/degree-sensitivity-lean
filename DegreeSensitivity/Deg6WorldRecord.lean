module

public import DegreeSensitivity.Deg6CertData1
public import DegreeSensitivity.Deg6CertData2
public import DegreeSensitivity.PrimeRegGraph
public import DegreeSensitivity.RigidityMoments

@[expose] public section

/-!
# New World Record: `B_6 ≤ 20` (Impossibility of `(n = 21, d = 6)`)

Complete, zero-`sorry`, zero-`native_decide` proof that every Boolean function of polynomial
degree `≤ 6` has maximum sensitivity `≤ 20` (strictly beating Wellens's 2022 record `B_6 ≤ 21`).

Proof structure:
1. **Steps 1–2 (`deg6_step12_bounds`)**: Six kernel-verified pure-integer Subset-`J` Terwilliger LP
   certificates (`Deg6CertData1`) force `S_2 = 210` (`p_2 = 1`), `S_20 = 21` (`p_20 = 1`),
   `S_21 = 0` (`p_21 = 0`), `S_19 = 210` (`p_19 = 1`), and `839 ≤ S_3 ≤ 842`.
2. **Unique Degree-6 Profile (`deg6_profile_affine`)**: The 15 seventh-difference equations
   `Δ^7 p(k) = 0` (`k = 0..14`) uniquely determine every `S_k` (`0 ≤ k ≤ 21`) as an exact affine
   function of `S_3`.
3. **Step 3a (PSD+LP Refutation)**: Three kernel-verified 2-stage Terwilliger PSD+LP Farkas
   certificates (`Deg6CertData2`) eliminate `S_3 ∈ {839, 842, 841}`.
4. **Step 3b (Exact Integer SOS Rigidity)**: For the unique surviving profile `S_3 = 840`, the
   kernel-verified PSD+LP bound `m(3, 3, 2) - m(3, 4, 3) < 17641 / 143640` forces
     `∑_P (pairDeg3 f P - 12)^2 + 3 * ∑_Q (2 * f(Q) - quadDeg3 f Q + 2)^2 < 2`.
   Because `∑_P (pairDeg3 f P - 12) = 0` is an integer sum, both sums of squares vanish identically:
   `pairDeg3 f P = 12` for all pairs `P` and `quadDeg3 f Q = 2 + 2 f(Q)` for all quads `Q`.
5. **Step 4 (Forbidden 7-Regular Graph on 20 Vertices)**: `exists_reg_trifree_2k2free_of_rigidity`
   (`RigidityMoments`) produces a 7-regular, triangle-free, induced-`2K₂`-free graph on `Fin 20`,
   contradicting `no_7reg_trifree_2k2free_20` (`PrimeRegGraph`).
-/

namespace DegreeSensitivity

open scoped BigOperators

/-! ### Part 1: Integrality & Sum-of-Squares Helpers -/

private lemma sum_boolToReal_eq_natCast {α : Type*} (S : Finset α) (g : α → Bool) :
    ∃ m : ℕ, ∑ x ∈ S, boolToReal (g x) = (m : ℝ) := by
  refine ⟨(S.filter (fun x => g x = true)).card, ?_⟩
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  cases g x <;> simp [boolToReal]

private lemma realLayerSum_eq_natCast {n : ℕ} (f : BooleanFun n) (k : ℕ) :
    ∃ s : ℕ, realLayerSum (fun x => boolToReal (f x)) k = (s : ℝ) :=
  sum_boolToReal_eq_natCast (hammingLayer n k) f

private lemma realLayerSum_eq_choose_mul_layerAvg {n k : ℕ} (f : BooleanFun n) (hk : k ≤ n) :
    realLayerSum (fun x => boolToReal (f x)) k =
      (Nat.choose n k : ℝ) * layerAvg (fun x => boolToReal (f x)) k := by
  have hc : (Nat.choose n k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  rw [layerAvg, mul_div_cancel₀ _ hc]

private lemma realLayerSum_le_choose {n k : ℕ} (f : BooleanFun n) (hk : k ≤ n) :
    realLayerSum (fun x => boolToReal (f x)) k ≤ (Nat.choose n k : ℝ) := by
  rw [realLayerSum_eq_choose_mul_layerAvg f hk]
  have hle := layerAvg_bool_le_one f k hk
  have hc : (0 : ℝ) ≤ (Nat.choose n k : ℝ) := Nat.cast_nonneg _
  nlinarith

private lemma int_sq_ge_one_of_ne_zero {a : ℤ} (ha : a ≠ 0) : (1 : ℤ) ≤ a ^ 2 := by
  rcases lt_or_gt_of_ne ha with h | h <;> nlinarith

/-- If an integer function `z` on a finite set `S` sums to `0`, then either `z ≡ 0` on `S`
or `2 ≤ ∑ x ∈ S, (z x)^2`. -/
private lemma sum_sq_eq_zero_or_ge_two {α : Type*} [DecidableEq α] (S : Finset α) (z : α → ℤ)
    (hsum : ∑ x ∈ S, z x = 0) :
    (∀ x ∈ S, z x = 0) ∨ 2 ≤ ∑ x ∈ S, (z x) ^ 2 := by
  by_cases hall : ∀ x ∈ S, z x = 0
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨x₀, hx₀S, hz₀⟩ := hall
    have hex1 : ∃ x₁ ∈ S, x₁ ≠ x₀ ∧ z x₁ ≠ 0 := by
      by_contra hnone
      push Not at hnone
      have hsingle : ∑ x ∈ S, z x = z x₀ :=
        Finset.sum_eq_single x₀ (fun y hy hne => hnone y hy hne) (fun h => absurd hx₀S h)
      exact hz₀ (hsingle.symm.trans hsum)
    obtain ⟨x₁, hx₁S, hne, hz₁⟩ := hex1
    have hsub : ({x₀, x₁} : Finset α) ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hx₀S
      · rw [Finset.mem_singleton.mp hx]; exact hx₁S
    have hle : ∑ x ∈ ({x₀, x₁} : Finset α), (z x) ^ 2 ≤ ∑ x ∈ S, (z x) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    rw [Finset.sum_pair hne.symm] at hle
    have hsq0 : 1 ≤ (z x₀) ^ 2 := int_sq_ge_one_of_ne_zero hz₀
    have hsq1 : 1 ≤ (z x₁) ^ 2 := int_sq_ge_one_of_ne_zero hz₁
    linarith

/-- For any integer function `z` on `S`, either `z ≡ 0` on `S` or `1 ≤ ∑ x ∈ S, (z x)^2`. -/
private lemma sum_sq_eq_zero_or_ge_one {α : Type*} [DecidableEq α] (S : Finset α) (z : α → ℤ) :
    (∀ x ∈ S, z x = 0) ∨ 1 ≤ ∑ x ∈ S, (z x) ^ 2 := by
  by_cases hall : ∀ x ∈ S, z x = 0
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨x₀, hx₀S, hz₀⟩ := hall
    have hsub : ({x₀} : Finset α) ⊆ S := Finset.singleton_subset_iff.mpr hx₀S
    have hle : ∑ x ∈ ({x₀} : Finset α), (z x) ^ 2 ≤ ∑ x ∈ S, (z x) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    rw [Finset.sum_singleton] at hle
    have hsq0 : 1 ≤ (z x₀) ^ 2 := int_sq_ge_one_of_ne_zero hz₀
    linarith

/-! ### Part 2: Steps 1–2 LP Bounds & Unique Degree-6 Layer Profile -/

private lemma deg6_diff7 (f : BooleanFun 21) (hf : polyDegree f ≤ 6) (k : ℕ) (hk : k + 7 ≤ 21) :
    -layerAvg (fun x => boolToReal (f x)) k +
    7 * layerAvg (fun x => boolToReal (f x)) (k + 1) -
    21 * layerAvg (fun x => boolToReal (f x)) (k + 2) +
    35 * layerAvg (fun x => boolToReal (f x)) (k + 3) -
    35 * layerAvg (fun x => boolToReal (f x)) (k + 4) +
    21 * layerAvg (fun x => boolToReal (f x)) (k + 5) -
    7 * layerAvg (fun x => boolToReal (f x)) (k + 6) +
    layerAvg (fun x => boolToReal (f x)) (k + 7) = 0 := by
  have h := layerAvg_finDiff_eq_zero f hf hk
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at h
  have hc0 : Nat.choose 7 0 = 1 := by decide
  have hc1 : Nat.choose 7 1 = 7 := by decide
  have hc2 : Nat.choose 7 2 = 21 := by decide
  have hc3 : Nat.choose 7 3 = 35 := by decide
  have hc4 : Nat.choose 7 4 = 35 := by decide
  have hc5 : Nat.choose 7 5 = 21 := by decide
  have hc6 : Nat.choose 7 6 = 7 := by decide
  have hc7 : Nat.choose 7 7 = 1 := by decide
  rw [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7] at h
  norm_num at h
  linarith

private lemma deg6_step12_bounds (f : BooleanFun 21) (hf : polyDegree f ≤ 6)
    (hf0 : f (zeroVec 21) = false) (hf1 : ∀ i : Fin 21, f (basisVec i) = true) :
    layerAvg (fun x => boolToReal (f x)) 2 = 1 ∧
    layerAvg (fun x => boolToReal (f x)) 19 = 1 ∧
    layerAvg (fun x => boolToReal (f x)) 20 = 1 ∧
    layerAvg (fun x => boolToReal (f x)) 21 = 0 ∧
    ∃ s3 : ℕ, 839 ≤ s3 ∧ s3 ≤ 842 ∧
      realLayerSum (fun x => boolToReal (f x)) 3 = (s3 : ℝ) := by
  set p : ℕ → ℝ := fun k => layerAvg (fun x => boolToReal (f x)) k
  -- Step 1a: S_2 > 209 ⇒ S_2 = 210 ⇒ p 2 = 1
  have hp2 : p 2 = 1 := by
    have hcert := layerAvg_bound_of_bino_cert_sliced f hf hf0 hf1 [] (by simp)
      step1aCert 2 1 step1aScale step1aLb step1aCert_u_ok step1aCert_c_ok
    have hsc : (0 : ℝ) < (step1aScale : ℝ) := by exact_mod_cast step1aScale_pos
    have hstr : (209 : ℝ) * (step1aScale : ℝ) < 210 * (step1aLb : ℝ) := by
      exact_mod_cast step1aLb_strict
    have hgt : (209 : ℝ) < 210 * p 2 := by
      dsimp only [p]; push_cast at hcert; nlinarith
    obtain ⟨s2, hs2⟩ := realLayerSum_eq_natCast f 2
    have hc2 : Nat.choose 21 2 = 210 := by rw [← fastChoose_eq]; decide
    have hsum := realLayerSum_eq_choose_mul_layerAvg f (k := 2) (by omega)
    rw [hs2, hc2] at hsum
    have hle := realLayerSum_le_choose f (k := 2) (by omega)
    rw [hs2, hc2] at hle
    norm_num at hsum hle
    have hs2_gt : (209 : ℝ) < (s2 : ℝ) := by dsimp only [p] at hgt; linarith
    have hs2_nat : s2 = 210 := by
      have h1 : 209 < s2 := by exact_mod_cast hs2_gt
      have h2 : s2 ≤ 210 := by exact_mod_cast hle
      omega
    rw [hs2_nat] at hsum; dsimp only [p]; norm_num at hsum; linarith
  -- Step 1b: S_20 > 20 ⇒ S_20 = 21 ⇒ p 20 = 1
  have hp20 : p 20 = 1 := by
    have hcert := layerAvg_bound_of_bino_cert_sliced f hf hf0 hf1 [] (by simp)
      step1bCert 20 1 step1bScale step1bLb step1bCert_u_ok step1bCert_c_ok
    have hsc : (0 : ℝ) < (step1bScale : ℝ) := by exact_mod_cast step1bScale_pos
    have hstr : (20 : ℝ) * (step1bScale : ℝ) < 21 * (step1bLb : ℝ) := by
      exact_mod_cast step1bLb_strict
    have hgt : (20 : ℝ) < 21 * p 20 := by
      dsimp only [p]; push_cast at hcert; nlinarith
    obtain ⟨s20, hs20⟩ := realLayerSum_eq_natCast f 20
    have hc20 : Nat.choose 21 20 = 21 := by rw [← fastChoose_eq]; decide
    have hsum := realLayerSum_eq_choose_mul_layerAvg f (k := 20) (by omega)
    rw [hs20, hc20] at hsum
    have hle := realLayerSum_le_choose f (k := 20) (by omega)
    rw [hs20, hc20] at hle
    norm_num at hsum hle
    have hs20_gt : (20 : ℝ) < (s20 : ℝ) := by dsimp only [p] at hgt; linarith
    have hs20_nat : s20 = 21 := by
      have h1 : 20 < s20 := by exact_mod_cast hs20_gt
      have h2 : s20 ≤ 21 := by exact_mod_cast hle
      omega
    rw [hs20_nat] at hsum; dsimp only [p]; norm_num at hsum; linarith
  -- Step 1c: S_21 < 1 ⇒ S_21 = 0 ⇒ p 21 = 0
  have hp21 : p 21 = 0 := by
    have hcert := layerAvg_bound_of_bino_cert_sliced f hf hf0 hf1 [] (by simp)
      step1cCert 21 (-1) step1cScale step1cLb step1cCert_u_ok step1cCert_c_ok
    have hsc : (0 : ℝ) < (step1cScale : ℝ) := by exact_mod_cast step1cScale_pos
    have hstr : -(step1cScale : ℝ) < (step1cLb : ℝ) := by
      have hR : ((-1 : ℤ) * (step1cScale : ℤ) : ℝ) < ((1 : ℤ) * step1cLb : ℝ) := by
        exact_mod_cast step1cLb_strict
      push_cast at hR; linarith
    have hlt : p 21 < 1 := by dsimp only [p]; push_cast at hcert; nlinarith
    obtain ⟨s21, hs21⟩ := realLayerSum_eq_natCast f 21
    have hc21 : Nat.choose 21 21 = 1 := by rw [← fastChoose_eq]; decide
    have hsum := realLayerSum_eq_choose_mul_layerAvg f (k := 21) (by omega)
    rw [hs21, hc21] at hsum
    norm_num at hsum
    have hs21_lt : (s21 : ℝ) < 1 := by dsimp only [p] at hlt; linarith
    have hs21_nat : s21 = 0 := by
      have h1 : s21 < 1 := by exact_mod_cast hs21_lt
      omega
    rw [hs21_nat] at hsum; dsimp only [p]; norm_num at hsum; linarith
  -- Now extraFix = [(2, 1), (20, 1), (21, 0)] holds!
  have hextra : ∀ q ∈ ([(2, 1), (20, 1), (21, 0)] : List (ℕ × ℕ)),
      layerAvg (fun x => boolToReal (f x)) q.1 = (q.2 : ℝ) := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · simpa using hp2
    · simpa using hp20
    · simpa using hp21
  -- Step 2a: S_19 > 209 ⇒ S_19 = 210 ⇒ p 19 = 1
  have hp19 : p 19 = 1 := by
    have hcert := layerAvg_bound_of_bino_cert_sliced f hf hf0 hf1 [(2, 1), (20, 1), (21, 0)] hextra
      step2aCert 19 1 step2aScale step2aLb step2aCert_u_ok step2aCert_c_ok
    have hsc : (0 : ℝ) < (step2aScale : ℝ) := by exact_mod_cast step2aScale_pos
    have hstr : (209 : ℝ) * (step2aScale : ℝ) < 210 * (step2aLb : ℝ) := by
      exact_mod_cast step2aLb_strict
    have hgt : (209 : ℝ) < 210 * p 19 := by
      dsimp only [p]; push_cast at hcert; nlinarith
    obtain ⟨s19, hs19⟩ := realLayerSum_eq_natCast f 19
    have hc19 : Nat.choose 21 19 = 210 := by rw [← fastChoose_eq]; decide
    have hsum := realLayerSum_eq_choose_mul_layerAvg f (k := 19) (by omega)
    rw [hs19, hc19] at hsum
    have hle := realLayerSum_le_choose f (k := 19) (by omega)
    rw [hs19, hc19] at hle
    norm_num at hsum hle
    have hs19_gt : (209 : ℝ) < (s19 : ℝ) := by dsimp only [p] at hgt; linarith
    have hs19_nat : s19 = 210 := by
      have h1 : 209 < s19 := by exact_mod_cast hs19_gt
      have h2 : s19 ≤ 210 := by exact_mod_cast hle
      omega
    rw [hs19_nat] at hsum; dsimp only [p]; norm_num at hsum; linarith
  -- Steps 2b & 2c: 838 < S_3 < 843 ⇒ 839 ≤ s3 ≤ 842
  obtain ⟨s3, hs3⟩ := realLayerSum_eq_natCast f 3
  have hc3 : Nat.choose 21 3 = 1330 := by rw [← fastChoose_eq]; decide
  have hsum3 := realLayerSum_eq_choose_mul_layerAvg f (k := 3) (by omega)
  rw [hs3, hc3] at hsum3
  norm_num at hsum3
  have hs3_ge : 839 ≤ s3 := by
    have hcert := layerAvg_bound_of_bino_cert_sliced f hf hf0 hf1 [(2, 1), (20, 1), (21, 0)] hextra
      step2bCert 3 1 step2bScale step2bLb step2bCert_u_ok step2bCert_c_ok
    have hsc : (0 : ℝ) < (step2bScale : ℝ) := by exact_mod_cast step2bScale_pos
    have hstr : (838 : ℝ) * (step2bScale : ℝ) < 1330 * (step2bLb : ℝ) := by
      exact_mod_cast step2bLb_strict
    have hgt : (838 : ℝ) < (s3 : ℝ) := by push_cast at hcert; nlinarith
    have h1 : 838 < s3 := by exact_mod_cast hgt
    omega
  have hs3_le : s3 ≤ 842 := by
    have hcert := layerAvg_bound_of_bino_cert_sliced f hf hf0 hf1 [(2, 1), (20, 1), (21, 0)] hextra
      step2cCert 3 (-1) step2cScale step2cLb step2cCert_u_ok step2cCert_c_ok
    have hsc : (0 : ℝ) < (step2cScale : ℝ) := by exact_mod_cast step2cScale_pos
    have hstr : (-843 : ℝ) * (step2cScale : ℝ) < 1330 * (step2cLb : ℝ) := by
      exact_mod_cast step2cLb_strict
    have hlt : (s3 : ℝ) < 843 := by push_cast at hcert; nlinarith
    have h1 : s3 < 843 := by exact_mod_cast hlt
    omega
  exact ⟨hp2, hp19, hp20, hp21, s3, hs3_ge, hs3_le, hs3⟩

/-- Fast binomial evaluations `C(21, k)` via `fastChoose`. -/
private lemma choose_21_val :
    Nat.choose 21 0 = 1 ∧ Nat.choose 21 1 = 21 ∧ Nat.choose 21 2 = 210 ∧
    Nat.choose 21 3 = 1330 ∧ Nat.choose 21 4 = 5985 ∧ Nat.choose 21 5 = 20349 ∧
    Nat.choose 21 6 = 54264 ∧ Nat.choose 21 7 = 116280 ∧ Nat.choose 21 8 = 203490 ∧
    Nat.choose 21 9 = 293930 ∧ Nat.choose 21 10 = 352716 ∧ Nat.choose 21 11 = 352716 ∧
    Nat.choose 21 12 = 293930 ∧ Nat.choose 21 13 = 203490 ∧ Nat.choose 21 14 = 116280 ∧
    Nat.choose 21 15 = 54264 ∧ Nat.choose 21 16 = 20349 ∧ Nat.choose 21 17 = 5985 ∧
    Nat.choose 21 18 = 1330 ∧ Nat.choose 21 19 = 210 ∧ Nat.choose 21 20 = 21 ∧
    Nat.choose 21 21 = 1 := by
  simp only [← fastChoose_eq]
  decide

/-- Unique affine determination of all 22 layer sums `S_k` from `(p_0, p_1, p_2, p_19, p_20, p_21)`
and `S_3 = s3` via the 15 seventh-difference equations `Δ^7 p(k) = 0`. -/
private lemma deg6_profile_affine (f : BooleanFun 21) (hf : polyDegree f ≤ 6)
    (hf0 : f (zeroVec 21) = false) (hf1 : ∀ i : Fin 21, f (basisVec i) = true)
    (hp2 : layerAvg (fun x => boolToReal (f x)) 2 = 1)
    (hp19 : layerAvg (fun x => boolToReal (f x)) 19 = 1)
    (hp20 : layerAvg (fun x => boolToReal (f x)) 20 = 1)
    (hp21 : layerAvg (fun x => boolToReal (f x)) 21 = 0)
    (s3 : ℝ) (hS3 : realLayerSum (fun x => boolToReal (f x)) 3 = s3) :
    realLayerSum (fun x => boolToReal (f x)) 0 = 0 ∧
    realLayerSum (fun x => boolToReal (f x)) 1 = 21 ∧
    realLayerSum (fun x => boolToReal (f x)) 2 = 210 ∧
    realLayerSum (fun x => boolToReal (f x)) 3 = s3 ∧
    realLayerSum (fun x => boolToReal (f x)) 4 = 15 * s3 - 11025 ∧
    realLayerSum (fun x => boolToReal (f x)) 5 = 105 * s3 - 86814 ∧
    realLayerSum (fun x => boolToReal (f x)) 6 = 455 * s3 - 377622 ∧
    realLayerSum (fun x => boolToReal (f x)) 7 = 1365 * s3 - 1115730 ∧
    realLayerSum (fun x => boolToReal (f x)) 8 = 3003 * s3 - 2416050 ∧
    realLayerSum (fun x => boolToReal (f x)) 9 = 5005 * s3 - 3980340 ∧
    realLayerSum (fun x => boolToReal (f x)) 10 = 6435 * s3 - 5087082 ∧
    realLayerSum (fun x => boolToReal (f x)) 11 = 6435 * s3 - 5087082 ∧
    realLayerSum (fun x => boolToReal (f x)) 12 = 5005 * s3 - 3980340 ∧
    realLayerSum (fun x => boolToReal (f x)) 13 = 3003 * s3 - 2416050 ∧
    realLayerSum (fun x => boolToReal (f x)) 14 = 1365 * s3 - 1115730 ∧
    realLayerSum (fun x => boolToReal (f x)) 15 = 455 * s3 - 377622 ∧
    realLayerSum (fun x => boolToReal (f x)) 16 = 105 * s3 - 86814 ∧
    realLayerSum (fun x => boolToReal (f x)) 17 = 15 * s3 - 11025 ∧
    realLayerSum (fun x => boolToReal (f x)) 18 = s3 ∧
    realLayerSum (fun x => boolToReal (f x)) 19 = 210 ∧
    realLayerSum (fun x => boolToReal (f x)) 20 = 21 ∧
    realLayerSum (fun x => boolToReal (f x)) 21 = 0 := by
  set p : ℕ → ℝ := fun k => layerAvg (fun x => boolToReal (f x)) k
  have hp0 : p 0 = 0 := layerAvg_bool_zero hf0
  have hp1 : p 1 = 1 := layerAvg_bool_one (by omega) hf1
  change p 2 = 1 at hp2
  change p 19 = 1 at hp19
  change p 20 = 1 at hp20
  change p 21 = 0 at hp21
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18,
    c19, c20, c21⟩ := choose_21_val
  have hp3 : p 3 = s3 / 1330 := by
    have hsum := realLayerSum_eq_choose_mul_layerAvg f (k := 3) (by omega)
    rw [hS3, c3] at hsum
    dsimp only [p]; norm_num at hsum; linarith
  have hd0 := deg6_diff7 f hf 0 (by omega)
  have hd1 := deg6_diff7 f hf 1 (by omega)
  have hd2 := deg6_diff7 f hf 2 (by omega)
  have hd3 := deg6_diff7 f hf 3 (by omega)
  have hd4 := deg6_diff7 f hf 4 (by omega)
  have hd5 := deg6_diff7 f hf 5 (by omega)
  have hd6 := deg6_diff7 f hf 6 (by omega)
  have hd7 := deg6_diff7 f hf 7 (by omega)
  have hd8 := deg6_diff7 f hf 8 (by omega)
  have hd9 := deg6_diff7 f hf 9 (by omega)
  have hd10 := deg6_diff7 f hf 10 (by omega)
  have hd11 := deg6_diff7 f hf 11 (by omega)
  have hd12 := deg6_diff7 f hf 12 (by omega)
  have hd13 := deg6_diff7 f hf 13 (by omega)
  have hd14 := deg6_diff7 f hf 14 (by omega)
  change -p 0 + 7 * p 1 - 21 * p 2 + 35 * p 3 - 35 * p 4 + 21 * p 5 - 7 * p 6 + p 7 = 0 at hd0
  change -p 1 + 7 * p 2 - 21 * p 3 + 35 * p 4 - 35 * p 5 + 21 * p 6 - 7 * p 7 + p 8 = 0 at hd1
  change -p 2 + 7 * p 3 - 21 * p 4 + 35 * p 5 - 35 * p 6 + 21 * p 7 - 7 * p 8 + p 9 = 0 at hd2
  change -p 3 + 7 * p 4 - 21 * p 5 + 35 * p 6 - 35 * p 7 + 21 * p 8 - 7 * p 9 + p 10 = 0 at hd3
  change -p 4 + 7 * p 5 - 21 * p 6 + 35 * p 7 - 35 * p 8 + 21 * p 9 - 7 * p 10 + p 11 = 0 at hd4
  change -p 5 + 7 * p 6 - 21 * p 7 + 35 * p 8 - 35 * p 9 + 21 * p 10 - 7 * p 11 + p 12 = 0 at hd5
  change -p 6 + 7 * p 7 - 21 * p 8 + 35 * p 9 - 35 * p 10 + 21 * p 11 - 7 * p 12 + p 13 = 0 at hd6
  change -p 7 + 7 * p 8 - 21 * p 9 + 35 * p 10 - 35 * p 11 + 21 * p 12 - 7 * p 13 + p 14 = 0 at hd7
  change -p 8 + 7 * p 9 - 21 * p 10 + 35 * p 11 - 35 * p 12 + 21 * p 13 - 7 * p 14 + p 15 = 0 at hd8
  change -p 9 + 7 * p 10 - 21 * p 11 + 35 * p 12 - 35 * p 13 + 21 * p 14 - 7 * p 15 + p 16 = 0 at hd9
  change -p 10 + 7 * p 11 - 21 * p 12 + 35 * p 13 - 35 * p 14 + 21 * p 15 - 7 * p 16 + p 17 = 0 at hd10
  change -p 11 + 7 * p 12 - 21 * p 13 + 35 * p 14 - 35 * p 15 + 21 * p 16 - 7 * p 17 + p 18 = 0 at hd11
  change -p 12 + 7 * p 13 - 21 * p 14 + 35 * p 15 - 35 * p 16 + 21 * p 17 - 7 * p 18 + p 19 = 0 at hd12
  change -p 13 + 7 * p 14 - 21 * p 15 + 35 * p 16 - 35 * p 17 + 21 * p 18 - 7 * p 19 + p 20 = 0 at hd13
  change -p 14 + 7 * p 15 - 21 * p 16 + 35 * p 17 - 35 * p 18 + 21 * p 19 - 7 * p 20 + p 21 = 0 at hd14
  rw [hp0, hp1, hp2] at hd0
  rw [hp1, hp2] at hd1
  rw [hp2] at hd2
  rw [hp19] at hd12
  rw [hp19, hp20] at hd13
  rw [hp19, hp20, hp21] at hd14
  have hp4 : p 4 = 10 / 3 * p 3 - 35 / 19 := by
    linear_combination (-68/133) * hd0 + (-68/57) * hd1 + (-104/57) * hd2 + (-130/57) * hd3 +
      (-143/57) * hd4 + (-143/57) * hd5 + (-44/19) * hd6 + (-264/133) * hd7 + (-30/19) * hd8 +
      (-22/19) * hd9 + (-44/57) * hd10 + (-26/57) * hd11 + (-13/57) * hd12 + (-5/57) * hd13 +
      (-8/399) * hd14
  have hp5 : p 5 = 350 / 51 * p 3 - 1378 / 323 := by
    linear_combination (-32/19) * hd0 + (-84/19) * hd1 + (-364/51) * hd2 + (-8918/969) * hd3 +
      (-10010/969) * hd4 + (-10153/969) * hd5 + (-3157/323) * hd6 + (-2728/323) * hd7 +
      (-2184/323) * hd8 + (-1610/323) * hd9 + (-1078/323) * hd10 + (-1918/969) * hd11 +
      (-962/969) * hd12 + (-371/969) * hd13 + (-5/57) * hd14
  have hp6 : p 6 = 2275 / 204 * p 3 - 8991 / 1292 := by
    linear_combination (-65/19) * hd0 + (-182/19) * hd1 + (-5278/323) * hd2 + (-84539/3876) * hd3 +
      (-97097/3876) * hd4 + (-25025/969) * hd5 + (-7876/323) * hd6 + (-13739/646) * hd7 +
      (-11081/646) * hd8 + (-4109/323) * hd9 + (-2765/323) * hd10 + (-6587/1292) * hd11 +
      (-9947/3876) * hd12 + (-962/969) * hd13 + (-13/57) * hd14
  have hp7 : p 7 = 3185 / 204 * p 3 - 12397 / 1292 := by linarith only [hd0, hp4, hp5, hp6]
  have hp8 : p 8 = 1001 / 51 * p 3 - 3835 / 323 := by linarith only [hd1, hp4, hp5, hp6, hp7]
  have hp9 : p 9 = 385 / 17 * p 3 - 4374 / 323 := by linarith only [hd2, hp4, hp5, hp6, hp7, hp8]
  have hp10 : p 10 = 825 / 34 * p 3 - 9317 / 646 := by
    linarith only [hd3, hp4, hp5, hp6, hp7, hp8, hp9]
  have hp11 : p 11 = 825 / 34 * p 3 - 9317 / 646 := by
    linarith only [hd4, hp4, hp5, hp6, hp7, hp8, hp9, hp10]
  have hp12 : p 12 = 385 / 17 * p 3 - 4374 / 323 := by
    linarith only [hd5, hp5, hp6, hp7, hp8, hp9, hp10, hp11]
  have hp13 : p 13 = 1001 / 51 * p 3 - 3835 / 323 := by
    linarith only [hd6, hp6, hp7, hp8, hp9, hp10, hp11, hp12]
  have hp14 : p 14 = 3185 / 204 * p 3 - 12397 / 1292 := by
    linarith only [hd7, hp7, hp8, hp9, hp10, hp11, hp12, hp13]
  have hp15 : p 15 = 2275 / 204 * p 3 - 8991 / 1292 := by
    linarith only [hd8, hp8, hp9, hp10, hp11, hp12, hp13, hp14]
  have hp16 : p 16 = 350 / 51 * p 3 - 1378 / 323 := by
    linarith only [hd9, hp9, hp10, hp11, hp12, hp13, hp14, hp15]
  have hp17 : p 17 = 10 / 3 * p 3 - 35 / 19 := by
    linarith only [hd10, hp10, hp11, hp12, hp13, hp14, hp15, hp16]
  have hp18 : p 18 = p 3 := by
    linarith only [hd11, hp11, hp12, hp13, hp14, hp15, hp16, hp17]
  have hS : ∀ k ≤ 21, realLayerSum (fun x => boolToReal (f x)) k = (Nat.choose 21 k : ℝ) * p k :=
    fun k hk => realLayerSum_eq_choose_mul_layerAvg f hk
  refine ⟨?_, ?_, ?_, hS3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hS 0 (by omega), c0, hp0]; norm_num
  · rw [hS 1 (by omega), c1, hp1]; norm_num
  · rw [hS 2 (by omega), c2, hp2]; norm_num
  · rw [hS 4 (by omega), c4, hp4, hp3]; norm_num; ring
  · rw [hS 5 (by omega), c5, hp5, hp3]; norm_num; ring
  · rw [hS 6 (by omega), c6, hp6, hp3]; norm_num; ring
  · rw [hS 7 (by omega), c7, hp7, hp3]; norm_num; ring
  · rw [hS 8 (by omega), c8, hp8, hp3]; norm_num; ring
  · rw [hS 9 (by omega), c9, hp9, hp3]; norm_num; ring
  · rw [hS 10 (by omega), c10, hp10, hp3]; norm_num; ring
  · rw [hS 11 (by omega), c11, hp11, hp3]; norm_num; ring
  · rw [hS 12 (by omega), c12, hp12, hp3]; norm_num; ring
  · rw [hS 13 (by omega), c13, hp13, hp3]; norm_num; ring
  · rw [hS 14 (by omega), c14, hp14, hp3]; norm_num; ring
  · rw [hS 15 (by omega), c15, hp15, hp3]; norm_num; ring
  · rw [hS 16 (by omega), c16, hp16, hp3]; norm_num; ring
  · rw [hS 17 (by omega), c17, hp17, hp3]; norm_num; ring
  · rw [hS 18 (by omega), c18, hp18, hp3]; norm_num; ring
  · rw [hS 19 (by omega), c19, hp19]; norm_num
  · rw [hS 20 (by omega), c20, hp20]; norm_num
  · rw [hS 21 (by omega), c21, hp21]; norm_num

private lemma le_21_cases {k : ℕ} (hk : k ≤ 21) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
    k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨
    k = 19 ∨ k = 20 ∨ k = 21 := by
  omega

/-! ### Part 3: Step 3 (PSD Refutation + SOS Rigidity) & Step 4 (Forbidden 7-Regular Graph) -/

/-- **Core Impossibility Theorem**: No normalized `(n = 21, d = 6)` Boolean function exists. -/
theorem no_normalized_deg6_dim21 :
    ¬ ∃ f : BooleanFun 21, polyDegree f ≤ 6 ∧
      f (zeroVec 21) = false ∧ ∀ i : Fin 21, f (basisVec i) = true := by
  rintro ⟨f, hf, hf0, hf1⟩
  obtain ⟨hp2, hp19, hp20, hp21, s3, hs3_ge, hs3_le, hS3⟩ := deg6_step12_bounds f hf hf0 hf1
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := deg6_profile_affine f hf hf0 hf1 hp2 hp19 hp20 hp21 (s3 : ℝ) hS3
  have hcases : s3 = 839 ∨ s3 = 840 ∨ s3 = 841 ∨ s3 = 842 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · -- Case `S_3 = 839`: eliminated by kernel-verified PSD + Farkas certificate `step3_839Cert`
    refine false_of_psd_bino_farkas_sliced f hf deg6S_839 ?_ step3_839Cert
      step3_839Cert_hdr_ok step3_839Cert_slices_ok
    intro k hk
    rcases le_21_cases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [deg6S_839] <;> norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
        h13, h14, h15, h16, h17, h18, h19, h20, h21]
  · -- Case `S_3 = 840`: PSD+LP bound + exact integer SOS rigidity → forbidden 7-regular graph on 20 vertices!
    have hS840 : ∀ k ≤ 21, realLayerSum (fun x => boolToReal (f x)) k = (deg6S_840 k : ℝ) := by
      intro k hk
      rcases le_21_cases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [deg6S_840] <;> norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
          h13, h14, h15, h16, h17, h18, h19, h20, h21]
    have hbound := targetM_bound_of_psd_bino_sliced f hf deg6S_840 hS840 step3_840Cert
      [(3, 4, 3, 1), (3, 3, 2, -1)] step3_840Scale step3_840Lb
      step3_840Cert_hdr_ok step3_840Cert_slices_ok
    simp only [evalTargetM, add_zero] at hbound
    have hsc : (0 : ℝ) < (step3_840Scale : ℝ) := by exact_mod_cast step3_840Scale_pos
    have hstr : (-17641 : ℝ) * (step3_840Scale : ℝ) < 143640 * (step3_840Lb : ℝ) := by
      exact_mod_cast step3_840Lb_strict
    -- Strict PSD+LP inequality: `287280 * (m(3,3,2) - m(3,4,3)) - 35280 < 2`!
    have hlp_strict : 287280 * (pairCorr f 3 3 2 - pairCorr f 3 4 3) - 35280 < 2 := by
      push_cast at hbound; nlinarith
    have hS3_840 : realLayerSum (fun x => boolToReal (f x)) 3 = 840 := by
      simpa using h3
    have hS4_1575 : realLayerSum (fun x => boolToReal (f x)) 4 = 1575 := by
      rw [h4]; norm_num
    set Pairs := Finset.powersetCard 2 (Finset.univ : Finset (Fin 21))
    set Quads := Finset.powersetCard 4 (Finset.univ : Finset (Fin 21))
    have hcardP : Pairs.card = 210 := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, ← fastChoose_eq]; decide
    have hcardQ : Quads.card = 5985 := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, ← fastChoose_eq]; decide
    have hpc332 : pairCount 21 3 3 2 = 71820 := by
      unfold pairCount; simp only [← fastChoose_eq]; decide
    have hpc343 : pairCount 21 3 4 3 = 23940 := by
      unfold pairCount; simp only [← fastChoose_eq]; decide
    have hpair_eq : ∑ P ∈ Pairs, (pairDeg3 f P - 12) ^ 2 = 71820 * pairCorr f 3 3 2 - 27720 := by
      have hm1 := sum_pairDeg3 f
      have hm2 := sum_pairDeg3_sq (n := 21) (by omega) f
      rw [hS3_840] at hm1 hm2; rw [hpc332] at hm2
      calc ∑ P ∈ Pairs, (pairDeg3 f P - 12) ^ 2
          = ∑ P ∈ Pairs, ((pairDeg3 f P) ^ 2 - 24 * pairDeg3 f P + 144) :=
            Finset.sum_congr rfl (fun _ _ => by ring)
        _ = (∑ P ∈ Pairs, (pairDeg3 f P) ^ 2) - 24 * (∑ P ∈ Pairs, pairDeg3 f P) +
              ∑ _P ∈ Pairs, (144 : ℝ) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        _ = 71820 * pairCorr f 3 3 2 - 27720 := by
            rw [hm2, hm1, Finset.sum_const, nsmul_eq_mul, hcardP]; norm_num; ring
    have hquad_eq : ∑ Q ∈ Quads, (2 * boolToReal (f (indicator Q)) - quadDeg3 f Q + 2) ^ 2 =
        71820 * pairCorr f 3 3 2 - 95760 * pairCorr f 3 4 3 - 2520 := by
      have hmf := sum_quad_f f
      have hmf2 : ∑ Q ∈ Quads, (boolToReal (f (indicator Q))) ^ 2 = 1575 := by
        calc ∑ Q ∈ Quads, (boolToReal (f (indicator Q))) ^ 2
            = ∑ Q ∈ Quads, boolToReal (f (indicator Q)) :=
              Finset.sum_congr rfl (fun Q _ => by cases f (indicator Q) <;> norm_num [boolToReal])
          _ = 1575 := by rw [hmf, hS4_1575]
      have hmt := sum_quadDeg3 f
      have hmft := sum_quad_f_mul_quadDeg3 (n := 21) (by omega) f
      have hmt2 := sum_quadDeg3_sq (n := 21) (by omega) f
      rw [hS4_1575] at hmf; rw [hS3_840] at hmt hmt2; rw [hpc343] at hmft; rw [hpc332] at hmt2
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
        _ = 71820 * pairCorr f 3 3 2 - 95760 * pairCorr f 3 4 3 - 2520 := by
            rw [hmf2, hmt2, hmft, hmf, hmt, Finset.sum_const, nsmul_eq_mul, hcardQ]; norm_num; ring
    -- Combined integer SOS sum is strictly `< 2`!
    have hsos_lt2 :
        (∑ P ∈ Pairs, (pairDeg3 f P - 12) ^ 2) +
        3 * (∑ Q ∈ Quads, (2 * boolToReal (f (indicator Q)) - quadDeg3 f Q + 2) ^ 2) < 2 := by
      linarith
    -- Lift `pairDeg3 f P - 12` and `2 f(Q) - quadDeg3 f Q + 2` to exact integers `zP`, `zQ`!
    have hzP_ex : ∀ P : Finset (Fin 21), ∃ z : ℤ, pairDeg3 f P - 12 = (z : ℝ) := by
      intro P
      obtain ⟨m, hm⟩ := sum_boolToReal_eq_natCast
        ((hammingLayer 21 3).filter (fun x => P ⊆ supportOf x)) f
      refine ⟨(m : ℤ) - 12, ?_⟩
      change (∑ x ∈ (hammingLayer 21 3).filter (fun x => P ⊆ supportOf x), boolToReal (f x)) - 12 = _
      rw [hm]; push_cast; rfl
    choose zP hzP using hzP_ex
    have hzQ_ex : ∀ Q : Finset (Fin 21),
        ∃ z : ℤ, 2 * boolToReal (f (indicator Q)) - quadDeg3 f Q + 2 = (z : ℝ) := by
      intro Q
      obtain ⟨m, hm⟩ := sum_boolToReal_eq_natCast
        ((hammingLayer 21 3).filter (fun x => supportOf x ⊆ Q)) f
      refine ⟨(if f (indicator Q) then 2 else 0) - (m : ℤ) + 2, ?_⟩
      change 2 * boolToReal (f (indicator Q)) -
        (∑ x ∈ (hammingLayer 21 3).filter (fun x => supportOf x ⊆ Q), boolToReal (f x)) + 2 = _
      rw [hm]; cases f (indicator Q) <;> simp [boolToReal]
    choose zQ hzQ using hzQ_ex
    have hzP_sum : ∑ P ∈ Pairs, zP P = 0 := by
      have hR : ((∑ P ∈ Pairs, zP P : ℤ) : ℝ) = 0 := by
        rw [Int.cast_sum]
        have heq : ∑ P ∈ Pairs, (zP P : ℝ) = ∑ P ∈ Pairs, (pairDeg3 f P - 12) :=
          Finset.sum_congr rfl (fun P _ => (hzP P).symm)
        rw [heq, Finset.sum_sub_distrib, sum_pairDeg3 f, hS3_840, Finset.sum_const,
          nsmul_eq_mul, hcardP]
        norm_num
      exact_mod_cast hR
    have hz_lt2 : (∑ P ∈ Pairs, (zP P) ^ 2) + 3 * (∑ Q ∈ Quads, (zQ Q) ^ 2) < 2 := by
      have hR : (((∑ P ∈ Pairs, (zP P) ^ 2) + 3 * (∑ Q ∈ Quads, (zQ Q) ^ 2) : ℤ) : ℝ) < (2 : ℤ) := by
        push_cast
        have hP : ∑ P ∈ Pairs, ((zP P : ℝ) ^ 2) = ∑ P ∈ Pairs, (pairDeg3 f P - 12) ^ 2 :=
          Finset.sum_congr rfl (fun P _ => by rw [hzP P])
        have hQ : ∑ Q ∈ Quads, ((zQ Q : ℝ) ^ 2) =
            ∑ Q ∈ Quads, (2 * boolToReal (f (indicator Q)) - quadDeg3 f Q + 2) ^ 2 :=
          Finset.sum_congr rfl (fun Q _ => by rw [hzQ Q])
        rw [hP, hQ]; exact hsos_lt2
      exact_mod_cast hR
    have hzP_nn : 0 ≤ ∑ P ∈ Pairs, (zP P) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hzQ_nn : 0 ≤ ∑ Q ∈ Quads, (zQ Q) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hzP_zero : ∀ P ∈ Pairs, zP P = 0 := by
      rcases sum_sq_eq_zero_or_ge_two Pairs zP hzP_sum with h | h
      · exact h
      · linarith
    have hzQ_zero : ∀ Q ∈ Quads, zQ Q = 0 := by
      rcases sum_sq_eq_zero_or_ge_one Quads zQ with h | h
      · exact h
      · linarith
    have hpair12 : ∀ P ∈ Pairs, pairDeg3 f P = ((12 : ℕ) : ℝ) := by
      intro P hP
      have h0 : pairDeg3 f P - 12 = 0 := by rw [hzP P, hzP_zero P hP]; norm_num
      norm_num; linarith
    have hquad_rig : ∀ Q ∈ Quads, quadDeg3 f Q = 2 + 2 * boolToReal (f (indicator Q)) := by
      intro Q hQ
      have h0 : 2 * boolToReal (f (indicator Q)) - quadDeg3 f Q + 2 = 0 := by
        rw [hzQ Q, hzQ_zero Q hQ]; norm_num
      linarith
    -- Step 4: Link graph on `Fin 20` is 7-regular, triangle-free, induced-`2K₂`-free — impossible!
    obtain ⟨adj, hirrefl, hsymm, hreg, htrifree, h2k2free⟩ :=
      exists_reg_trifree_2k2free_of_rigidity (m := 20) (d0 := 12) (r := 7) (by omega) f hpair12 hquad_rig
    exact no_7reg_trifree_2k2free_20 adj hirrefl hsymm hreg htrifree h2k2free
  · -- Case `S_3 = 841`: eliminated by kernel-verified PSD + Farkas certificate `step3_841Cert`
    refine false_of_psd_bino_farkas_sliced f hf deg6S_841 ?_ step3_841Cert
      step3_841Cert_hdr_ok step3_841Cert_slices_ok
    intro k hk
    rcases le_21_cases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [deg6S_841] <;> norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
        h13, h14, h15, h16, h17, h18, h19, h20, h21]
  · -- Case `S_3 = 842`: eliminated by kernel-verified PSD + Farkas certificate `step3_842Cert`
    refine false_of_psd_bino_farkas_sliced f hf deg6S_842 ?_ step3_842Cert
      step3_842Cert_hdr_ok step3_842Cert_slices_ok
    intro k hk
    rcases le_21_cases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [deg6S_842] <;> norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
        h13, h14, h15, h16, h17, h18, h19, h20, h21]

/-- **World Record `B_6 ≤ 20`**: Every Boolean function of polynomial degree `≤ 6` has maximum
sensitivity `≤ 20` (strictly beating Wellens 2022 `B_6 ≤ 21`). -/
theorem maxSensitivity_le_twenty_of_deg_le_six_proof {m : ℕ} (f : BooleanFun m)
    (hf : polyDegree f ≤ 6) : maxSensitivity f ≤ 20 := by
  have hlt := maxSensitivity_lt_of_no_normalized (k := 21) (d := 6) no_normalized_deg6_dim21 m f hf
  omega

end DegreeSensitivity
