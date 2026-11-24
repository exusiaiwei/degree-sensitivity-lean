module

public import DegreeSensitivity.Symmetrisation
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# Universal Polynomial Upper Bound: `s(f) ≤ 4 * deg(f)^3`

Using the Symmetrisation Lemma (`symmetrisation_polynomial`), the Mean Value Theorem,
and Chebyshev orthogonality (`Polynomial.Chebyshev`), we prove that every Boolean
function `f : BooleanFun n` satisfies

  `maxSensitivity f ≤ 4 * (polyDegree f) ^ 3`.

In particular, the set of valid asymptotic degree–sensitivity exponents in the
definition of `degSensitivityExponent` (`C_37`) is nonempty (containing `3`),
establishing `degSensitivityExponent ≤ 3`.
-/

namespace DegreeSensitivity

open scoped BigOperators
open Polynomial Polynomial.Chebyshev Real MeasureTheory

private lemma abs_sin_nat_mul_le (n : ℕ) (θ : ℝ) : |Real.sin (n * θ)| ≤ n * |Real.sin θ| := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    rw [add_mul, one_mul, Real.sin_add]
    calc |Real.sin (n * θ) * Real.cos θ + Real.cos (n * θ) * Real.sin θ|
        ≤ |Real.sin (n * θ) * Real.cos θ| + |Real.cos (n * θ) * Real.sin θ| := abs_add_le _ _
      _ = |Real.sin (n * θ)| * |Real.cos θ| + |Real.cos (n * θ)| * |Real.sin θ| := by
          rw [abs_mul, abs_mul]
      _ ≤ |Real.sin (n * θ)| * 1 + 1 * |Real.sin θ| := by
          gcongr
          · exact Real.abs_cos_le_one θ
          · exact Real.abs_cos_le_one (n * θ)
      _ ≤ (n * |Real.sin θ|) * 1 + 1 * |Real.sin θ| := by gcongr
      _ = (n + 1) * |Real.sin θ| := by ring

private lemma abs_eval_U_le (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(U ℝ m).eval x| ≤ (m + 1 : ℝ) := by
  have hx1 : -1 ≤ x := hx.1
  have hx2 : x ≤ 1 := hx.2
  by_cases h1 : x = 1
  · subst h1
    have hval : (U ℝ m).eval 1 = (m + 1 : ℝ) := by
      induction m using Nat.strong_induction_on with
      | _ k ih =>
        match k with
        | 0 => simp
        | 1 => simp; norm_num
        | k + 2 =>
          have hrec := U_add_two ℝ (k : ℤ)
          have h1' := ih (k + 1) (by omega)
          have h0' := ih k (by omega)
          have hev := congrArg (Polynomial.eval (1 : ℝ)) hrec
          simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
            Polynomial.eval_X, mul_one] at hev
          push_cast at hev h1' h0' ⊢
          linarith
    rw [hval, abs_of_nonneg (by positivity)]
  · by_cases hm1 : x = -1
    · subst hm1
      have hval : (U ℝ m).eval (-1) = (-1 : ℝ) ^ m * (m + 1 : ℝ) := by
        induction m using Nat.strong_induction_on with
        | _ k ih =>
          match k with
          | 0 => simp
          | 1 => simp; norm_num
          | k + 2 =>
            have hrec := U_add_two ℝ (k : ℤ)
            have h1' := ih (k + 1) (by omega)
            have h0' := ih k (by omega)
            have hev := congrArg (Polynomial.eval (-1 : ℝ)) hrec
            simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
              Polynomial.eval_X] at hev
            push_cast at hev h1' h0' ⊢
            rw [hev, h1', h0']
            ring
      rw [hval, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (by positivity)]
    · let θ := Real.arccos x
      have hcos : Real.cos θ = x := Real.cos_arccos hx1 hx2
      have hsin_pos : 0 < Real.sin θ := by
        rw [Real.sin_arccos]
        apply Real.sqrt_pos.mpr
        have hlt1 : x < 1 := lt_of_le_of_ne hx2 h1
        have hgt1 : -1 < x := lt_of_le_of_ne hx1 (Ne.symm hm1)
        nlinarith
      have hU := U_real_cos (θ := θ) (n := (m : ℤ))
      rw [hcos] at hU
      have hmul : |(U ℝ m).eval x| * |Real.sin θ| ≤ (m + 1 : ℝ) * |Real.sin θ| := by
        rw [← abs_mul, hU]
        have := abs_sin_nat_mul_le (m + 1) θ
        simpa [Nat.cast_add, Nat.cast_one] using this
      exact le_of_mul_le_mul_right hmul (abs_pos.mpr hsin_pos.ne')

private lemma abs_eval_deriv_T_le (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(T ℝ k).derivative.eval x| ≤ (k : ℝ) ^ 2 := by
  cases k with
  | zero =>
    simp
  | succ m =>
    have hderiv := T_derivative_eq_U (R := ℝ) ((m + 1 : ℕ) : ℤ)
    have hsub : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by omega
    rw [hsub] at hderiv
    rw [hderiv, Polynomial.eval_mul, Polynomial.eval_intCast, abs_mul]
    have hU := abs_eval_U_le m hx
    have hcast : |(((m + 1 : ℕ) : ℤ) : ℝ)| = ((m + 1 : ℕ) : ℝ) := by
      rw [Int.cast_natCast, abs_of_nonneg (by positivity)]
    rw [hcast]
    calc ((m + 1 : ℕ) : ℝ) * |(U ℝ m).eval x|
        ≤ ((m + 1 : ℕ) : ℝ) * (m + 1 : ℝ) := by gcongr
      _ = ((m + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring

/-- Derivative bound on `[-1, 1]` via Chebyshev expansion:
if `q : ℝ[X]` has `q.natDegree ≤ d` and `|q.eval x| ≤ M` on `[-1, 1]` (with `0 ≤ M`),
then `|q.derivative.eval x| ≤ 2 * (d : ℝ)^3 * M` on `[-1, 1]`. -/
theorem poly_deriv_bound_chebyshev {d : ℕ} {q : ℝ[X]} (hq : q.natDegree ≤ d)
    {M : ℝ} (hM : 0 ≤ M) (hbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |q.eval x| ≤ M) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, |q.derivative.eval x| ≤ 2 * (d : ℝ) ^ 3 * M := by
  have hmem : q ∈ Polynomial.degreeLT ℝ (d + 1) := by
    rw [Polynomial.mem_degreeLT]
    exact lt_of_le_of_lt (Polynomial.degree_le_natDegree) (by exact_mod_cast Nat.lt_succ_of_le hq)
  rw [← Polynomial.Sequence.span_degreeLT (chebyshevTsequence ℝ) (by simp),
    show Set.Iio (d + 1) = (Finset.range (d + 1) : Set ℕ) by ext; simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, hq_eq⟩ := hmem
  -- Bound each coefficient `|c k| ≤ 2 * M` for `1 ≤ k ≤ d` using Chebyshev orthogonality.
  have hc_bound : ∀ k ∈ Finset.range (d + 1), 1 ≤ k → |c k| ≤ 2 * M := by
    intro k hk hk1
    have hkne : k ≠ 0 := by omega
    have hint_eq : ∫ x, q.eval x * (T ℝ k).eval x ∂measureT = c k * (π / 2) := by
      have hexp : ∀ x, q.eval x * (T ℝ k).eval x =
          ∑ i ∈ Finset.range (d + 1), c i * ((T ℝ i).eval x * (T ℝ k).eval x) := by
        intro x
        rw [← hq_eq, Polynomial.eval_finsetSum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        simp only [chebyshevTsequence, Polynomial.eval_smul, smul_eq_mul]
        ring
      simp_rw [hexp]
      rw [MeasureTheory.integral_finsetSum]
      · simp_rw [MeasureTheory.integral_const_mul]
        rw [Finset.sum_eq_single k]
        · rw [integral_T_real_mul_self_measureT_of_ne_zero hkne]
        · intro i _ hik
          rw [integral_eval_T_real_mul_eval_T_real_measureT_of_ne hik, mul_zero]
        · intro hnot; exact absurd hk hnot
      · intro i _
        apply integrable_measureT
        exact (Continuous.mul continuous_const
          (Continuous.mul (T ℝ i).continuous (T ℝ k).continuous)).continuousOn
    have hint_abs : |∫ x, q.eval x * (T ℝ k).eval x ∂measureT| ≤ M * π := by
      rw [integral_measureT_eq_integral_cos]
      calc |∫ θ in (0 : ℝ)..π, q.eval (Real.cos θ) * (T ℝ k).eval (Real.cos θ)|
          ≤ ∫ θ in (0 : ℝ)..π, |q.eval (Real.cos θ) * (T ℝ k).eval (Real.cos θ)| :=
            intervalIntegral.abs_integral_le_integral_abs Real.pi_nonneg
        _ ≤ ∫ _θ in (0 : ℝ)..π, M := by
            apply intervalIntegral.integral_mono_on Real.pi_nonneg
            · exact (Continuous.abs (Continuous.mul (q.continuous.comp Real.continuous_cos)
                ((T ℝ k).continuous.comp Real.continuous_cos))).intervalIntegrable 0 π
            · exact continuous_const.intervalIntegrable 0 π
            · intro θ _
              rw [abs_mul, T_real_cos]
              have hcos_mem : Real.cos θ ∈ Set.Icc (-1 : ℝ) 1 :=
                ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
              calc |q.eval (Real.cos θ)| * |Real.cos ((k : ℤ) * θ)|
                  ≤ M * 1 := mul_le_mul (hbnd _ hcos_mem) (Real.abs_cos_le_one _)
                    (abs_nonneg _) hM
                _ = M := mul_one M
        _ = M * π := by simp [mul_comm]
    rw [hint_eq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < π / 2)] at hint_abs
    have hpi : 0 < π := Real.pi_pos
    nlinarith
  -- Now differentiate `q = ∑ i ∈ range (d + 1), c i • T ℝ i` and apply triangle inequality.
  intro x hx
  have hderiv_eq : q.derivative =
      ∑ i ∈ Finset.range (d + 1), c i • (T ℝ i).derivative := by
    rw [← hq_eq, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [chebyshevTsequence]
  rw [hderiv_eq, Polynomial.eval_finsetSum]
  calc |∑ i ∈ Finset.range (d + 1), (c i • (T ℝ i).derivative).eval x|
      ≤ ∑ i ∈ Finset.range (d + 1), |(c i • (T ℝ i).derivative).eval x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (d + 1), |c i| * |(T ℝ i).derivative.eval x| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Polynomial.eval_smul, smul_eq_mul, abs_mul]
    _ ≤ ∑ i ∈ Finset.range (d + 1), (if i = 0 then (0 : ℝ) else 2 * M * (d : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hi0 : i = 0
        · subst hi0; simp
        · simp only [hi0, ↓reduceIte]
          have hi1 : 1 ≤ i := Nat.pos_of_ne_zero hi0
          have hid : (i : ℝ) ≤ (d : ℝ) := by
            exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hci : |c i| ≤ 2 * M := hc_bound i hi hi1
          have hTi : |(T ℝ i).derivative.eval x| ≤ (d : ℝ) ^ 2 :=
            (abs_eval_deriv_T_le i hx).trans (by nlinarith)
          exact mul_le_mul hci hTi (abs_nonneg _) (by positivity)
    _ ≤ 2 * (d : ℝ) ^ 3 * M := by
        cases d with
        | zero => simp
        | succ d' =>
          rw [Finset.sum_range_succ']
          simp only [↓reduceIte, add_zero, Nat.succ_ne_zero, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
          push_cast
          ring_nf
          exact le_refl _

/-- **Universal Polynomial Upper Bound (`s(f) ≤ 4 * deg(f)^3`)**:
Every Boolean function `f : BooleanFun n` satisfies `maxSensitivity f ≤ 4 * (polyDegree f) ^ 3`. -/
theorem maxSensitivity_le_four_mul_cube {n : ℕ} (f : BooleanFun n) :
    maxSensitivity f ≤ 4 * (polyDegree f) ^ 3 := by
  set d := polyDegree f with hd_def
  set s := maxSensitivity f with hs_def
  by_cases hs0 : s = 0
  · simp [hs0]
  have hs_pos : 1 ≤ s := Nat.pos_of_ne_zero hs0
  have hd_pos : 1 ≤ d := by
    by_contra hlt
    have hd0 : d = 0 := by omega
    exact hs0 (maxSensitivity_eq_zero_of_polyDegree_zero hd0)
  have hsR_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos
  -- Step 1: Restrict to a normalized `s`-bit function `g` of degree `≤ d`, then symmetrise.
  obtain ⟨g, hgdeg, hg0, hg1⟩ := exists_normalized_subfunction f (le_refl s)
  obtain ⟨p, hpdeg, hpeval⟩ := symmetrisation_polynomial g hgdeg
  have hp0 : p.eval 0 = 0 := by
    have := hpeval 0 (Nat.zero_le s)
    rw [Nat.cast_zero, layerAvg_bool_zero hg0] at this
    exact this
  have hp1 : p.eval 1 = 1 := by
    have := hpeval 1 hs_pos
    rw [Nat.cast_one, layerAvg_bool_one hs_pos hg1] at this
    exact this
  have hpbnd : ∀ k ≤ s, 0 ≤ p.eval (k : ℝ) ∧ p.eval (k : ℝ) ≤ 1 := fun k hk => by
    rw [hpeval k hk]
    exact ⟨layerAvg_bool_nonneg g k, layerAvg_bool_le_one g k hk⟩
  -- Step 2: Rescale `t = (s / 2) * (x + 1)` from `[-1, 1]` to `[0, s]` and shift `[0, 1]` to `[-1, 1]`.
  let L : ℝ[X] := Polynomial.C ((s : ℝ) / 2) * (Polynomial.X + 1)
  let q : ℝ[X] := 2 * p.comp L - 1
  have hq_eval : ∀ x : ℝ, q.eval x = 2 * p.eval ((s : ℝ) / 2 * (x + 1)) - 1 := by
    intro x
    simp [q, L]
  have hq_deg : q.natDegree ≤ d := by
    have hLdeg : L.natDegree ≤ 1 := by
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      simp
    have hcomp : (p.comp L).natDegree ≤ d := by
      calc (p.comp L).natDegree ≤ p.natDegree * L.natDegree := Polynomial.natDegree_comp_le
        _ ≤ d * 1 := Nat.mul_le_mul hpdeg hLdeg
        _ = d := mul_one d
    dsimp only [q]
    rw [sub_eq_add_neg]
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    rw [Polynomial.natDegree_neg, Polynomial.natDegree_one]
    refine max_le ?_ (Nat.zero_le d)
    have h2 : (2 : ℝ[X]) = Polynomial.C 2 := rfl
    rw [h2]
    exact (Polynomial.natDegree_C_mul_le _ _).trans hcomp
  -- Step 3: Achieve maxima `M = max_{[-1, 1]} |q|` and `D = max_{[-1, 1]} |q'|`.
  have hcomp_Icc : IsCompact (Set.Icc (-1 : ℝ) 1) := isCompact_Icc
  have hne_Icc : (Set.Icc (-1 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨xM, hxM_mem, hxM_max⟩ := hcomp_Icc.exists_isMaxOn hne_Icc
    (Continuous.abs q.continuous).continuousOn
  obtain ⟨xD, hxD_mem, hxD_max⟩ := hcomp_Icc.exists_isMaxOn hne_Icc
    (Continuous.abs q.derivative.continuous).continuousOn
  set M := |q.eval xM|
  set D := |q.derivative.eval xD|
  have hM_nonneg : 0 ≤ M := abs_nonneg _
  have hM_le : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |q.eval x| ≤ M := fun x hx => hxM_max hx
  have hD_le : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |q.derivative.eval x| ≤ D := fun x hx => hxD_max hx
  -- Step 4a: Mean Value Theorem on `[-1, -1 + 2 / s]` yields `s ≤ D`.
  have hs_le_D : (s : ℝ) ≤ D := by
    let a : ℝ := -1
    let b : ℝ := -1 + 2 / (s : ℝ)
    have hab : a < b := by
      dsimp [a, b]
      have : (0 : ℝ) < 2 / (s : ℝ) := by positivity
      linarith
    have hb_le1 : b ≤ 1 := by
      dsimp [b]
      have h1s : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_pos
      have : 2 / (s : ℝ) ≤ 2 := by rw [div_le_iff₀ hsR_pos]; linarith
      linarith
    have hcont : ContinuousOn (fun x => q.eval x) (Set.Icc a b) := q.continuous.continuousOn
    have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt (fun x => q.eval x) (q.derivative.eval x) x :=
      fun x _ => q.hasDerivAt x
    obtain ⟨ξ, hξ_mem, hξ_eq⟩ := exists_hasDerivAt_eq_slope (fun x => q.eval x)
      (fun x => q.derivative.eval x) hab hcont hderiv
    have hqa : q.eval a = -1 := by
      rw [hq_eval]; dsimp [a]; norm_num [hp0]
    have hqb : q.eval b = 1 := by
      rw [hq_eval]; dsimp [b]
      have harg : (s : ℝ) / 2 * (-1 + 2 / (s : ℝ) + 1) = 1 := by field_simp [hsR_pos.ne']; ring
      rw [harg, hp1]; norm_num
    have hslope : q.derivative.eval ξ = (s : ℝ) := by
      rw [hξ_eq, hqa, hqb]
      dsimp [a, b]
      field_simp [hsR_pos.ne']
      ring
    have hξ_Icc : ξ ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt hξ_mem.1, (le_of_lt hξ_mem.2).trans hb_le1⟩
    calc (s : ℝ) = |q.derivative.eval ξ| := by rw [hslope, abs_of_pos hsR_pos]
      _ ≤ D := hD_le ξ hξ_Icc
  -- Step 4b: Nearest-integer MVT bound gives `M ≤ 1 + D / s`.
  have hM_le_bound : M ≤ 1 + D / (s : ℝ) := by
    let t := (s : ℝ) / 2 * (xM + 1)
    have ht0 : 0 ≤ t := by
      have : 0 ≤ xM + 1 := by linarith [hxM_mem.1]
      positivity
    have hts : t ≤ (s : ℝ) := by
      have : xM + 1 ≤ 2 := by linarith [hxM_mem.2]
      dsimp [t]; nlinarith
    let k : ℕ := min s (Nat.floor (t + 1 / 2))
    have hk_le : k ≤ s := Nat.min_le_left _ _
    have ht_dist : |t - (k : ℝ)| ≤ 1 / 2 := by
      by_cases hfl : Nat.floor (t + 1 / 2) ≤ s
      · have hk_eq : k = Nat.floor (t + 1 / 2) := Nat.min_eq_right hfl
        rw [hk_eq]
        have h1 : (Nat.floor (t + 1 / 2) : ℝ) ≤ t + 1 / 2 := Nat.floor_le (by linarith)
        have h2 : t + 1 / 2 < (Nat.floor (t + 1 / 2) : ℝ) + 1 := Nat.lt_floor_add_one _
        rw [abs_le]; constructor <;> linarith
      · have hk_eq : k = s := Nat.min_eq_left (Nat.le_of_not_ge hfl)
        rw [hk_eq]
        have hs_lt : (s : ℝ) < (Nat.floor (t + 1 / 2) : ℝ) := by
          exact_mod_cast Nat.lt_of_not_ge hfl
        have h1 : (Nat.floor (t + 1 / 2) : ℝ) ≤ t + 1 / 2 := Nat.floor_le (by linarith)
        rw [abs_le]; constructor <;> linarith
    let xk : ℝ := 2 * (k : ℝ) / (s : ℝ) - 1
    have hxk_mem : xk ∈ Set.Icc (-1 : ℝ) 1 := by
      dsimp [xk]
      have hkR : (k : ℝ) ≤ (s : ℝ) := by exact_mod_cast hk_le
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      constructor
      · have : 0 ≤ 2 * (k : ℝ) / (s : ℝ) := by positivity
        linarith
      · have : 2 * (k : ℝ) / (s : ℝ) ≤ 2 := by rw [div_le_iff₀ hsR_pos]; linarith
        linarith
    have hqxk_abs : |q.eval xk| ≤ 1 := by
      rw [hq_eval]
      have harg : (s : ℝ) / 2 * (xk + 1) = (k : ℝ) := by
        dsimp [xk]; field_simp [hsR_pos.ne']; ring
      rw [harg]
      obtain ⟨h0, h1⟩ := hpbnd k hk_le
      rw [abs_le]; constructor <;> linarith
    have hx_dist : |xM - xk| ≤ 1 / (s : ℝ) := by
      have hrel : xM - xk = (2 / (s : ℝ)) * (t - (k : ℝ)) := by
        dsimp [t, xk]; field_simp [hsR_pos.ne']; ring
      rw [hrel, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / (s : ℝ))]
      calc 2 / (s : ℝ) * |t - (k : ℝ)| ≤ 2 / (s : ℝ) * (1 / 2) := by gcongr
        _ = 1 / (s : ℝ) := by ring
    have hdiff : |q.eval xM - q.eval xk| ≤ D * |xM - xk| := by
      rcases lt_trichotomy xM xk with hlt | heq | hgt
      · obtain ⟨ξ, hξ, hξ_eq⟩ := exists_hasDerivAt_eq_slope (fun x => q.eval x)
          (fun x => q.derivative.eval x) hlt q.continuous.continuousOn (fun x _ => q.hasDerivAt x)
        have hξ_Icc : ξ ∈ Set.Icc (-1 : ℝ) 1 :=
          ⟨hxM_mem.1.trans (le_of_lt hξ.1), (le_of_lt hξ.2).trans hxk_mem.2⟩
        have hsub : q.eval xk - q.eval xM = q.derivative.eval ξ * (xk - xM) := by
          rw [hξ_eq, div_mul_cancel₀ _ (sub_ne_zero.mpr hlt.ne')]
        rw [abs_sub_comm, hsub, abs_mul, abs_sub_comm xk xM]
        exact mul_le_mul_of_nonneg_right (hD_le ξ hξ_Icc) (abs_nonneg _)
      · simp [heq]
      · obtain ⟨ξ, hξ, hξ_eq⟩ := exists_hasDerivAt_eq_slope (fun x => q.eval x)
          (fun x => q.derivative.eval x) hgt q.continuous.continuousOn (fun x _ => q.hasDerivAt x)
        have hξ_Icc : ξ ∈ Set.Icc (-1 : ℝ) 1 :=
          ⟨hxk_mem.1.trans (le_of_lt hξ.1), (le_of_lt hξ.2).trans hxM_mem.2⟩
        have hsub : q.eval xM - q.eval xk = q.derivative.eval ξ * (xM - xk) := by
          rw [hξ_eq, div_mul_cancel₀ _ (sub_ne_zero.mpr hgt.ne')]
        rw [hsub, abs_mul]
        exact mul_le_mul_of_nonneg_right (hD_le ξ hξ_Icc) (abs_nonneg _)
    calc M = |q.eval xM| := rfl
      _ = |(q.eval xM - q.eval xk) + q.eval xk| := by ring_nf
      _ ≤ |q.eval xM - q.eval xk| + |q.eval xk| := abs_add_le _ _
      _ ≤ D * |xM - xk| + 1 := by linarith
      _ ≤ D * (1 / (s : ℝ)) + 1 := by
          have hD0 : 0 ≤ D := abs_nonneg _
          gcongr
      _ = 1 + D / (s : ℝ) := by ring
  -- Step 4c: Chebyshev derivative bound gives `D ≤ 2 * d^3 * M`.
  have hD_le_cheb : D ≤ 2 * (d : ℝ) ^ 3 * M :=
    poly_deriv_bound_chebyshev hq_deg hM_nonneg hM_le xD hxD_mem
  -- Step 5: Combine `s ≤ D`, `M ≤ 1 + D / s`, `D ≤ 2 * d^3 * M` → `s ≤ 4 * d^3`.
  have hD_pos : 0 < D := lt_of_lt_of_le hsR_pos hs_le_D
  have hstep : (s : ℝ) * D ≤ 4 * (d : ℝ) ^ 3 * D := by
    have h1 : D ≤ 2 * (d : ℝ) ^ 3 * (1 + D / (s : ℝ)) := by
      have : (0 : ℝ) ≤ 2 * (d : ℝ) ^ 3 := by positivity
      exact hD_le_cheb.trans (mul_le_mul_of_nonneg_left hM_le_bound this)
    have h2 : (s : ℝ) * D ≤ 2 * (d : ℝ) ^ 3 * ((s : ℝ) + D) := by
      have hmul := mul_le_mul_of_nonneg_left h1 hsR_pos.le
      have hsimp : (s : ℝ) * (2 * (d : ℝ) ^ 3 * (1 + D / (s : ℝ))) =
          2 * (d : ℝ) ^ 3 * ((s : ℝ) + D) := by
        field_simp [hsR_pos.ne']
      linarith
    have h3 : 2 * (d : ℝ) ^ 3 * ((s : ℝ) + D) ≤ 2 * (d : ℝ) ^ 3 * (D + D) := by
      have : (0 : ℝ) ≤ 2 * (d : ℝ) ^ 3 := by positivity
      nlinarith
    linarith
  have hs_leR : (s : ℝ) ≤ 4 * (d : ℝ) ^ 3 := le_of_mul_le_mul_right hstep hD_pos
  exact_mod_cast hs_leR

/-- The exponent set in `degSensitivityExponent` is nonempty (contains `3` with constant `C = 4`). -/
theorem degSensitivityExponent_set_nonempty :
    { α : ℝ | ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : BooleanFun n),
      1 ≤ polyDegree f → (maxSensitivity f : ℝ) ≤ C * (polyDegree f : ℝ) ^ α }.Nonempty := by
  refine ⟨3, 4, by norm_num, fun n f _ => ?_⟩
  have h := maxSensitivity_le_four_mul_cube f
  have hR : (maxSensitivity f : ℝ) ≤ 4 * ((polyDegree f : ℝ) ^ (3 : ℕ)) := by exact_mod_cast h
  simpa [Real.rpow_natCast] using hR

end DegreeSensitivity
