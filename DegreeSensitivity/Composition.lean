module

public import DegreeSensitivity.ChebyshevBound
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# Boolean Function Composition and Asymptotic Exponent Lower Bounds

We define standard composition `composeBool f g : BooleanFun (n * m)` of Boolean
functions, prove that it multiplies sensitivity (on normalized witnesses) and is
submultiplicative in polynomial degree (`polyDegree (composeBool f g) ≤ polyDegree f * polyDegree g`),
and deduce by iterated composition `iterCompose` that ANY normalized witness `(n, d)` with
`2 ≤ n` and `2 ≤ d` establishes the asymptotic lower bound

  `Real.log n / Real.log d ≤ degSensitivityExponent`.

We also provide `polyDegree_comp_equiv` (invariance under coordinate relabeling) and a
general weighted-composition degree bound (`polyDegree_weightedCompose_le`) ready for
weighted-degree constructions such as `(n = 13, d = 5)`.
-/

namespace DegreeSensitivity

open scoped BigOperators
open MvPolynomial

/-- Relabeling input coordinates by an equivalence preserves `polyDegree`. -/
theorem polyDegree_comp_equiv {n m : ℕ} (e : Fin m ≃ Fin n) (f : BooleanFun n) :
    polyDegree (fun x : Fin m → Bool => f (fun i => x (e.symm i))) = polyDegree f := by
  have hle : ∀ {a b : ℕ} (e' : Fin b ≃ Fin a) (g : BooleanFun a),
      polyDegree (fun x : Fin b → Bool => g (fun i => x (e'.symm i))) ≤ polyDegree g := by
    intro a b e' g
    rw [polyDegree_le_iff]
    obtain ⟨P, hrep, hdeg⟩ := polyDegree_le_iff.mp (le_refl (polyDegree g))
    refine ⟨MvPolynomial.aeval (fun i => MvPolynomial.X (e'.symm i)) P, ?_, ?_⟩
    · intro x
      change MvPolynomial.eval (fun j => boolToReal (x j))
        (MvPolynomial.aeval (fun i => MvPolynomial.X (e'.symm i)) P) =
        boolToReal (g (fun i => x (e'.symm i)))
      rw [eval_aeval_eq]
      simpa [boolToReal] using hrep (fun i => x (e'.symm i))
    · refine (totalDegree_aeval_le _ P (fun i => by simp [MvPolynomial.totalDegree_X])).trans hdeg
  apply le_antisymm (hle e f)
  have hback := hle e.symm (fun x : Fin m → Bool => f (fun i => x (e.symm i)))
  have hfun : (fun x : Fin n → Bool => f (fun i => x (e (e.symm i)))) = f := by
    funext x; congr; funext i; simp
  simpa [Equiv.symm_symm, hfun] using hback

/-- Composition `(f ∘ g) : BooleanFun (n * m)` of Boolean functions `f : BooleanFun n`
and `g : BooleanFun m`, using the canonical product equivalence `finProdFinEquiv`. -/
def composeBool {n m : ℕ} (f : BooleanFun n) (g : BooleanFun m) : BooleanFun (n * m) :=
  fun x => f (fun i => g (fun j => x (finProdFinEquiv (i, j))))

lemma composeBool_zero {n m : ℕ} {f : BooleanFun n} {g : BooleanFun m}
    (hf0 : f (zeroVec n) = false) (hg0 : g (zeroVec m) = false) :
    composeBool f g (zeroVec (n * m)) = false := by
  change f (fun _ => g (zeroVec m)) = false
  have hinner : (fun _ : Fin n => g (zeroVec m)) = zeroVec n := by
    funext _; exact hg0
  rw [hinner, hf0]

lemma composeBool_basis {n m : ℕ} {f : BooleanFun n} {g : BooleanFun m}
    (hg0 : g (zeroVec m) = false)
    (hf1 : ∀ i : Fin n, f (basisVec i) = true)
    (hg1 : ∀ j : Fin m, g (basisVec j) = true) :
    ∀ k : Fin (n * m), composeBool f g (basisVec k) = true := by
  intro k
  let p := finProdFinEquiv.symm k
  have hp : finProdFinEquiv p = k := finProdFinEquiv.apply_symm_apply k
  have hinner : (fun i : Fin n => g (fun j : Fin m => basisVec k (finProdFinEquiv (i, j)))) =
      basisVec p.1 := by
    funext i
    rw [basisVec_apply]
    by_cases hi : i = p.1
    · subst hi
      have harg : (fun j : Fin m => basisVec k (finProdFinEquiv (p.1, j))) = basisVec p.2 := by
        funext j
        rw [basisVec_apply, basisVec_apply, ← hp]
        have hiff : (finProdFinEquiv (p.1, j) = finProdFinEquiv p) ↔ (j = p.2) := by
          rw [Equiv.apply_eq_iff_eq, Prod.ext_iff]
          simp
        simp [hiff]
      rw [harg, hg1 p.2]
      simp
    · have harg : (fun j : Fin m => basisVec k (finProdFinEquiv (i, j))) = zeroVec m := by
        funext j
        rw [basisVec_apply, ← hp]
        have hne : finProdFinEquiv (i, j) ≠ finProdFinEquiv p := by
          intro h
          have hpair := finProdFinEquiv.injective h
          exact hi (congrArg Prod.fst hpair)
        simp [zeroVec, hne]
      rw [harg, hg0]
      simp [hi]
  rw [composeBool, hinner, hf1 p.1]

/-- Degree submultiplicativity under Boolean composition:
`polyDegree (composeBool f g) ≤ polyDegree f * polyDegree g`. -/
theorem polyDegree_composeBool_le {n m : ℕ} (f : BooleanFun n) (g : BooleanFun m) :
    polyDegree (composeBool f g) ≤ polyDegree f * polyDegree g := by
  rw [polyDegree_le_iff]
  obtain ⟨P, hPrep, hPdeg⟩ := polyDegree_le_iff.mp (le_refl (polyDegree f))
  obtain ⟨Q, hQrep, hQdeg⟩ := polyDegree_le_iff.mp (le_refl (polyDegree g))
  let φ : Fin n → MvPolynomial (Fin (n * m)) ℝ := fun i =>
    MvPolynomial.rename (fun j : Fin m => finProdFinEquiv (i, j)) Q
  refine ⟨MvPolynomial.aeval φ P, ?_, ?_⟩
  · intro x
    change MvPolynomial.eval (fun k => boolToReal (x k)) (MvPolynomial.aeval φ P) =
      boolToReal (composeBool f g x)
    rw [eval_aeval_eq]
    have harg : (fun i => MvPolynomial.eval (fun k => boolToReal (x k)) (φ i)) =
        (fun i => boolToReal (g (fun j => x (finProdFinEquiv (i, j))))) := by
      funext i
      dsimp only [φ]
      rw [MvPolynomial.eval_rename]
      exact hQrep (fun j => x (finProdFinEquiv (i, j)))
    rw [harg]
    exact hPrep (fun i => g (fun j => x (finProdFinEquiv (i, j))))
  · have hφdeg : ∀ i : Fin n, (φ i).totalDegree ≤ polyDegree g := fun i =>
      (MvPolynomial.totalDegree_rename_le _ Q).trans hQdeg
    calc (MvPolynomial.aeval φ P).totalDegree
        ≤ polyDegree g * P.totalDegree := totalDegree_aeval_le_mul φ P (polyDegree g) hφdeg
      _ ≤ polyDegree g * polyDegree f := Nat.mul_le_mul_left _ hPdeg
      _ = polyDegree f * polyDegree g := mul_comm _ _

/-- Iterated composition `f^{\circ (k+1)} : BooleanFun (n ^ (k + 1))`. -/
def iterCompose {n : ℕ} (f : BooleanFun n) : (k : ℕ) → BooleanFun (n ^ (k + 1))
  | 0 => fun x => f (fun i => x (finCongr (pow_one n).symm i))
  | k + 1 => fun x =>
      composeBool (iterCompose f k) f
        (fun i => x (finCongr (pow_succ n (k + 1)).symm i))

private lemma iterCompose_props {n d : ℕ} (f : BooleanFun n)
    (hfdeg : polyDegree f ≤ d)
    (hf0 : f (zeroVec n) = false)
    (hf1 : ∀ i : Fin n, f (basisVec i) = true) :
    ∀ k : ℕ,
      polyDegree (iterCompose f k) ≤ d ^ (k + 1) ∧
      iterCompose f k (zeroVec (n ^ (k + 1))) = false ∧
      ∀ i : Fin (n ^ (k + 1)), iterCompose f k (basisVec i) = true := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · have heq := polyDegree_comp_equiv (finCongr (pow_one n)) f
      have hfun : (fun x : Fin (n ^ 1) → Bool => f (fun i => x ((finCongr (pow_one n)).symm i))) =
          iterCompose f 0 := rfl
      rw [hfun] at heq
      rw [heq, pow_one]
      exact hfdeg
    · exact hf0
    · intro i
      have harg : (fun j : Fin n => basisVec i ((finCongr (pow_one n)).symm j)) =
          basisVec (finCongr (pow_one n) i) := by
        funext j
        rw [basisVec_apply, basisVec_apply]
        have hiff : ((finCongr (pow_one n)).symm j = i) ↔ (j = finCongr (pow_one n) i) :=
          Equiv.symm_apply_eq (finCongr (pow_one n))
        exact decide_eq_decide.mpr hiff
      dsimp only [iterCompose]
      change f (fun j => basisVec i ((finCongr (pow_one n)).symm j)) = true
      rw [harg, hf1]
  | succ k ih =>
    obtain ⟨ih_deg, ih_0, ih_1⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · have heq := polyDegree_comp_equiv (finCongr (pow_succ n (k + 1)))
        (composeBool (iterCompose f k) f)
      have hfun : (fun x : Fin (n ^ (k + 2)) → Bool =>
          composeBool (iterCompose f k) f
            (fun i => x ((finCongr (pow_succ n (k + 1))).symm i))) = iterCompose f (k + 1) := rfl
      rw [hfun] at heq
      rw [heq]
      calc polyDegree (composeBool (iterCompose f k) f)
          ≤ polyDegree (iterCompose f k) * polyDegree f := polyDegree_composeBool_le _ _
        _ ≤ d ^ (k + 1) * d := Nat.mul_le_mul ih_deg hfdeg
        _ = d ^ (k + 2) := (pow_succ d (k + 1)).symm
    · exact composeBool_zero ih_0 hf0
    · intro i
      have harg : (fun j : Fin (n ^ (k + 1) * n) =>
          basisVec i ((finCongr (pow_succ n (k + 1))).symm j)) =
          basisVec (finCongr (pow_succ n (k + 1)) i) := by
        funext j
        rw [basisVec_apply, basisVec_apply]
        have hiff : ((finCongr (pow_succ n (k + 1))).symm j = i) ↔
            (j = finCongr (pow_succ n (k + 1)) i) :=
          Equiv.symm_apply_eq (finCongr (pow_succ n (k + 1)))
        exact decide_eq_decide.mpr hiff
      dsimp only [iterCompose]
      change composeBool (iterCompose f k) f
        (fun j => basisVec i ((finCongr (pow_succ n (k + 1))).symm j)) = true
      rw [harg]
      exact composeBool_basis hf0 ih_1 hf1 _

private lemma exists_pow_gt_of_one_lt {r : ℝ} (hr : 1 < r) (C : ℝ) : ∃ k : ℕ, C < r ^ k := by
  have hpos : 0 < r - 1 := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((C - 1) / (r - 1))
  refine ⟨k, ?_⟩
  have h1 : C - 1 < (k : ℝ) * (r - 1) := (div_lt_iff₀ hpos).mp hk
  have hbern : 1 + (k : ℝ) * (r - 1) ≤ (1 + (r - 1)) ^ k :=
    one_add_mul_le_pow (by linarith) k
  have hr_eq : (1 + (r - 1)) ^ k = r ^ k := by ring
  linarith

/-- **Composition Lower Bound Theorem for Tao's Constant #37a**:
Any normalized Boolean function `f : BooleanFun n` with `2 ≤ n`, `2 ≤ d`, `polyDegree f ≤ d`,
`f 0 = false`, and `∀ i, f (e_i) = true` implies

  `Real.log n / Real.log d ≤ degSensitivityExponent`. -/
theorem degSensitivityExponent_ge_log_div_log {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d)
    (f : BooleanFun n) (hfdeg : polyDegree f ≤ d)
    (hf0 : f (zeroVec n) = false) (hf1 : ∀ i : Fin n, f (basisVec i) = true) :
    Real.log (n : ℝ) / Real.log (d : ℝ) ≤ degSensitivityExponent := by
  apply le_csInf degSensitivityExponent_set_nonempty
  rintro α ⟨C, hCpos, hC⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hd_pos : (0 : ℝ) < (d : ℝ) := by positivity
  have h1n : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have h1d : (1 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 1 < d)
  have hlogd_pos : 0 < Real.log (d : ℝ) := Real.log_pos h1d
  -- Step 1: Every `k` gives a witness `g_k = iterCompose f k` with `s = n^(k+1)` and `1 ≤ deg ≤ d^(k+1)`.
  have hiter : ∀ k : ℕ,
      1 ≤ polyDegree (iterCompose f k) ∧
      polyDegree (iterCompose f k) ≤ d ^ (k + 1) ∧
      maxSensitivity (iterCompose f k) = n ^ (k + 1) := by
    intro k
    obtain ⟨hdegk, h0k, h1k⟩ := iterCompose_props f hfdeg hf0 hf1 k
    have hsens : maxSensitivity (iterCompose f k) = n ^ (k + 1) :=
      maxSensitivity_eq_dim_of_normalized h0k h1k
    have hdeg1 : 1 ≤ polyDegree (iterCompose f k) := by
      by_contra hlt
      have h0 : polyDegree (iterCompose f k) = 0 := by omega
      have hs0 := maxSensitivity_eq_zero_of_polyDegree_zero h0
      rw [hsens] at hs0
      have hpos : 0 < n ^ (k + 1) := pow_pos (by omega) _
      omega
    exact ⟨hdeg1, hdegk, hsens⟩
  -- Step 2: `0 ≤ α` (if `α < 0`, then `n^(k+1) ≤ C` for all `k`, impossible).
  have hα_nonneg : 0 ≤ α := by
    by_contra hneg
    have hαlt : α < 0 := lt_of_not_ge hneg
    obtain ⟨k, hk⟩ := exists_pow_gt_of_one_lt h1n C
    obtain ⟨hdeg1, _, hsens⟩ := hiter k
    have hbound := hC (n ^ (k + 1)) (iterCompose f k) hdeg1
    rw [hsens] at hbound
    have hpow_le : (polyDegree (iterCompose f k) : ℝ) ^ α ≤ 1 := by
      have h1 : (1 : ℝ) ≤ (polyDegree (iterCompose f k) : ℝ) := by exact_mod_cast hdeg1
      exact Real.rpow_le_one_of_one_le_of_nonpos h1 hαlt.le
    have hnk : (n : ℝ) ^ k ≤ (n : ℝ) ^ (k + 1) := by
      rw [pow_succ]
      have : (0 : ℝ) ≤ (n : ℝ) ^ k := by positivity
      nlinarith
    have hbound' : ((n : ℝ) ^ (k + 1)) ≤ C := by
      have hcast : ((n ^ (k + 1) : ℕ) : ℝ) = (n : ℝ) ^ (k + 1) := by push_cast; rfl
      rw [hcast] at hbound
      nlinarith
    linarith
  -- Step 3: Show `Real.log n / Real.log d ≤ α` by contradiction using `exists_pow_gt`.
  by_contra hlt
  have hαlt : α < Real.log (n : ℝ) / Real.log (d : ℝ) := lt_of_not_ge hlt
  have hmul : α * Real.log (d : ℝ) < Real.log (n : ℝ) := (lt_div_iff₀ hlogd_pos).mp hαlt
  have hdα_lt_n : (d : ℝ) ^ α < (n : ℝ) := by
    rw [Real.rpow_def_of_pos hd_pos, mul_comm]
    calc Real.exp (α * Real.log (d : ℝ)) < Real.exp (Real.log (n : ℝ)) :=
          Real.exp_lt_exp.mpr hmul
      _ = (n : ℝ) := Real.exp_log hn_pos
  have hdα_pos : 0 < (d : ℝ) ^ α := Real.rpow_pos_of_pos hd_pos α
  let r : ℝ := (n : ℝ) / (d : ℝ) ^ α
  have hr1 : 1 < r := (one_lt_div hdα_pos).mpr hdα_lt_n
  obtain ⟨k, hk⟩ := exists_pow_gt_of_one_lt hr1 C
  obtain ⟨hdeg1, hdegk, hsens⟩ := hiter k
  have hbound := hC (n ^ (k + 1)) (iterCompose f k) hdeg1
  rw [hsens] at hbound
  have hdeg_rpow : (polyDegree (iterCompose f k) : ℝ) ^ α ≤ ((d : ℝ) ^ α) ^ (k + 1) := by
    have hleR : (polyDegree (iterCompose f k) : ℝ) ≤ (d : ℝ) ^ (k + 1) := by
      exact_mod_cast hdegk
    calc (polyDegree (iterCompose f k) : ℝ) ^ α
        ≤ ((d : ℝ) ^ (k + 1)) ^ α := Real.rpow_le_rpow (Nat.cast_nonneg _) hleR hα_nonneg
      _ = (d : ℝ) ^ (((k + 1 : ℕ) : ℝ) * α) := by
          rw [← Real.rpow_natCast (d : ℝ) (k + 1), ← Real.rpow_mul hd_pos.le]
      _ = ((d : ℝ) ^ α) ^ (k + 1) := by
          rw [mul_comm, Real.rpow_mul hd_pos.le, Real.rpow_natCast]
  have hnk : (n : ℝ) ^ (k + 1) ≤ C * ((d : ℝ) ^ α) ^ (k + 1) := by
    have hcast : ((n ^ (k + 1) : ℕ) : ℝ) = (n : ℝ) ^ (k + 1) := by push_cast; rfl
    rw [hcast] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_left hdeg_rpow hCpos.le)
  have hr_pow : r ^ (k + 1) ≤ C := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos hdα_pos _)).mpr hnk
  have hr_mono : r ^ k ≤ r ^ (k + 1) := by
    rw [pow_succ]
    have : 0 ≤ r ^ k := by positivity
    nlinarith
  linarith

/-- **Weighted Composition Degree Bound**:
Suppose an outer Boolean function `g : BooleanFun m` has weighted multilinear degree `≤ D`
under positive weights `w : Fin m → ℕ` (i.e. `mobiusCoeff g S = 0` whenever `∑ i ∈ S, w i > D`),
and we substitute polynomials `φ i : MvPolynomial (Fin N) ℝ` representing inner functions
`h i : BooleanFun N` with `(φ i).totalDegree ≤ w i`.
Then the composed Boolean function `f x := g (fun i => h i x)` has `polyDegree f ≤ D`! -/
theorem polyDegree_weightedCompose_le {m N D : ℕ} (g : BooleanFun m)
    (w : Fin m → ℕ) (h : Fin m → BooleanFun N)
    (hg_wdeg : ∀ S : Finset (Fin m), D < ∑ i ∈ S, w i → mobiusCoeff g S = 0)
    (hh_deg : ∀ i : Fin m, polyDegree (h i) ≤ w i) :
    polyDegree (fun x : Fin N → Bool => g (fun i => h i x)) ≤ D := by
  classical
  rw [polyDegree_le_iff]
  have hpolys : ∀ i : Fin m, ∃ Q : MvPolynomial (Fin N) ℝ,
      RepresentsPoly Q (h i) ∧ Q.totalDegree ≤ w i :=
    fun i => polyDegree_le_iff.mp (hh_deg i)
  choose φ hφrep hφdeg using hpolys
  let P : MvPolynomial (Fin N) ℝ :=
    ∑ S : Finset (Fin m), MvPolynomial.C (mobiusCoeff g S : ℝ) * ∏ i ∈ S, φ i
  refine ⟨P, ?_, ?_⟩
  · intro x
    change MvPolynomial.eval (fun j => boolToReal (x j)) P =
      boolToReal (g (fun i => h i x))
    have hrep_g := representsPoly_mobius g (fun i => h i x)
    change MvPolynomial.eval (fun i => boolToReal (h i x))
      (multilinearPoly (fun S => (mobiusCoeff g S : ℝ))) = boolToReal (g (fun i => h i x)) at hrep_g
    rw [← hrep_g]
    simp only [P, multilinearPoly, monomialPoly, map_sum, map_mul, map_prod,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    apply Finset.sum_congr rfl
    intro S _
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact hφrep i x
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
    rw [Finset.sup_le_iff]
    intro S _
    by_cases hS : ∑ i ∈ S, w i ≤ D
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
      calc ∑ i ∈ S, (φ i).totalDegree ≤ ∑ i ∈ S, w i := Finset.sum_le_sum (fun i _ => hφdeg i)
        _ ≤ D := hS
    · have h0 : mobiusCoeff g S = 0 := hg_wdeg S (Nat.lt_of_not_ge hS)
      simp [h0]

end DegreeSensitivity
