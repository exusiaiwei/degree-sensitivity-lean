module

public import DegreeSensitivity.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Data.Finset.Powerset

@[expose] public section

/-!
# Multilinear Polynomial Representation and Möbius Inversion

Every Boolean function `f : {0, 1}^n → {0, 1}` is uniquely represented on `{0, 1}^n`
by a multilinear polynomial whose coefficients are given by integer Möbius inversion
on the Boolean lattice `Finset (Fin n)`. Moreover, `polyDegree f` equals the maximum
cardinality of a subset with nonzero Möbius coefficient.
-/

namespace DegreeSensitivity

open scoped BigOperators
open MvPolynomial

/-- Convert a Boolean value to `0` or `1` in `ℝ`. -/
def boolToReal (b : Bool) : ℝ := if b then 1 else 0

/-- Convert a Boolean value to `0` or `1` in `ℤ`. -/
def boolToInt (b : Bool) : ℤ := if b then 1 else 0

@[simp] lemma boolToReal_false : boolToReal false = 0 := rfl
@[simp] lemma boolToReal_true : boolToReal true = 1 := rfl
@[simp] lemma boolToInt_false : boolToInt false = 0 := rfl
@[simp] lemma boolToInt_true : boolToInt true = 1 := rfl

lemma boolToReal_eq_cast (b : Bool) : boolToReal b = (boolToInt b : ℝ) := by
  cases b <;> simp

lemma boolToReal_pow {b : Bool} {k : ℕ} (hk : k ≠ 0) :
    (boolToReal b) ^ k = boolToReal b := by
  cases b
  · simp [zero_pow hk]
  · simp

/-- The characteristic vector of a subset `S : Finset (Fin n)`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ S)

/-- The support of a bitstring `x : Fin n → Bool`. -/
def supportOf {n : ℕ} (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i = true)

@[simp] lemma mem_supportOf {n : ℕ} {x : Fin n → Bool} {i : Fin n} :
    i ∈ supportOf x ↔ x i = true := by
  simp [supportOf]

@[simp] lemma indicator_supportOf {n : ℕ} (x : Fin n → Bool) :
    indicator (supportOf x) = x := by
  funext i
  simp [indicator, supportOf]

@[simp] lemma supportOf_indicator {n : ℕ} (S : Finset (Fin n)) :
    supportOf (indicator S) = S := by
  ext i
  simp [indicator, supportOf]

/-- The multilinear monomial `∏ i ∈ S, X i`. -/
noncomputable def monomialPoly {n : ℕ} (S : Finset (Fin n)) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ S, MvPolynomial.X i

/-- The exponent `Finsupp` corresponding to a subset `S : Finset (Fin n)` (`1` on `S`, `0` off `S`). -/
noncomputable def subsetExp {n : ℕ} (S : Finset (Fin n)) : Fin n →₀ ℕ :=
  Finsupp.indicator S (fun _ _ => 1)

lemma subsetExp_apply {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    subsetExp S i = if i ∈ S then 1 else 0 := by
  by_cases hi : i ∈ S <;> simp [subsetExp, hi]

lemma subsetExp_empty {n : ℕ} : subsetExp (∅ : Finset (Fin n)) = 0 := by
  ext i
  simp [subsetExp_apply]

lemma subsetExp_support {n : ℕ} (S : Finset (Fin n)) :
    (subsetExp S).support = S := by
  ext i
  simp [subsetExp_apply]

lemma subsetExp_injective {n : ℕ} : Function.Injective (@subsetExp n) := by
  intro S T h
  have := congrArg Finsupp.support h
  simpa [subsetExp_support] using this

lemma subsetExp_sum {n : ℕ} (S : Finset (Fin n)) :
    (subsetExp S).sum (fun _ k => k) = S.card := by
  rw [Finsupp.sum, subsetExp_support]
  calc ∑ i ∈ S, subsetExp S i = ∑ _i ∈ S, (1 : ℕ) :=
        Finset.sum_congr rfl (fun i hi => by simp [subsetExp_apply, hi])
    _ = S.card := by simp

lemma monomialPoly_eq_monomial {n : ℕ} (S : Finset (Fin n)) :
    monomialPoly S = MvPolynomial.monomial (subsetExp S) (1 : ℝ) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [monomialPoly, Finset.prod_empty, subsetExp_empty, MvPolynomial.monomial_zero', map_one]
  | insert a s ha ih =>
    rw [monomialPoly, Finset.prod_insert ha, ← monomialPoly, ih, MvPolynomial.X,
      MvPolynomial.monomial_mul_monomial, one_mul]
    apply congrArg (fun e => MvPolynomial.monomial e (1 : ℝ))
    ext i
    rw [Finsupp.add_apply, Finsupp.single_apply, subsetExp_apply, subsetExp_apply]
    by_cases hia : a = i
    · subst hia
      simp [ha]
    · have hia' : i ≠ a := Ne.symm hia
      by_cases his : i ∈ s <;> simp [hia, hia', his]

lemma eval_monomialPoly {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    MvPolynomial.eval (fun i => boolToReal (x i)) (monomialPoly S) =
      if S ⊆ supportOf x then 1 else 0 := by
  rw [monomialPoly, map_prod]
  simp only [MvPolynomial.eval_X]
  by_cases h : S ⊆ supportOf x
  · simp only [h, ↓reduceIte]
    exact Finset.prod_eq_one (fun i hi => by
      have hx : x i = true := (mem_supportOf).mp (h hi)
      simp [hx])
  · simp only [h, ↓reduceIte]
    rw [Finset.not_subset] at h
    obtain ⟨i, hiS, hix⟩ := h
    have hx : x i = false := by
      cases hxi : x i
      · rfl
      · exact absurd (mem_supportOf.mpr hxi) hix
    exact Finset.prod_eq_zero hiS (by simp [hx])

lemma totalDegree_monomialPoly {n : ℕ} (S : Finset (Fin n)) :
    (monomialPoly S).totalDegree = S.card := by
  rw [monomialPoly_eq_monomial, MvPolynomial.totalDegree_monomial _ one_ne_zero, subsetExp_sum]

/-- Build the multilinear polynomial `∑ S, c S * ∏ i ∈ S, X i`. -/
noncomputable def multilinearPoly {n : ℕ} (c : Finset (Fin n) → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ S : Finset (Fin n), MvPolynomial.C (c S) * monomialPoly S

lemma coeff_multilinearPoly {n : ℕ} (c : Finset (Fin n) → ℝ) (e : Fin n →₀ ℕ) :
    (multilinearPoly c).coeff e =
      if e = subsetExp e.support then c e.support else 0 := by
  classical
  rw [multilinearPoly, MvPolynomial.coeff_sum]
  simp_rw [monomialPoly_eq_monomial, MvPolynomial.C_mul_monomial, mul_one, MvPolynomial.coeff_monomial]
  by_cases he : e = subsetExp e.support
  · rw [ite_eq_left_iff.mpr (fun h => absurd he h)]
    rw [Finset.sum_eq_single e.support]
    · exact ite_eq_left_iff.mpr (fun h => absurd he.symm h)
    · intro S _ hS
      have hne : subsetExp S ≠ e := by
        intro hEq
        apply hS
        have := congrArg Finsupp.support hEq
        simpa [subsetExp_support] using this
      exact ite_eq_right_iff.mpr (fun h => absurd h hne)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [ite_eq_right_iff.mpr (fun h => absurd h he)]
    apply Finset.sum_eq_zero
    intro S _
    have hne : subsetExp S ≠ e := by
      intro hEq
      apply he
      have hsupp : S = e.support := by
        have := congrArg Finsupp.support hEq
        simpa [subsetExp_support] using this
      rw [← hsupp, hEq]
    exact ite_eq_right_iff.mpr (fun h => absurd h hne)

lemma coeff_multilinearPoly_subsetExp {n : ℕ} (c : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    (multilinearPoly c).coeff (subsetExp S) = c S := by
  rw [coeff_multilinearPoly, subsetExp_support]
  simp

lemma eval_multilinearPoly {n : ℕ} (c : Finset (Fin n) → ℝ) (x : Fin n → Bool) :
    MvPolynomial.eval (fun i => boolToReal (x i)) (multilinearPoly c) =
      ∑ S ∈ (supportOf x).powerset, c S := by
  rw [multilinearPoly, map_sum]
  simp_rw [map_mul, MvPolynomial.eval_C, eval_monomialPoly, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext S
  simp [Finset.mem_powerset]

lemma totalDegree_multilinearPoly_le {n : ℕ} (c : Finset (Fin n) → ℝ) (d : ℕ)
    (hc : ∀ S : Finset (Fin n), d < S.card → c S = 0) :
    (multilinearPoly c).totalDegree ≤ d := by
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro e he
  rw [MvPolynomial.mem_support_iff, coeff_multilinearPoly] at he
  split_ifs at he with hEq
  · have hcard : e.support.card ≤ d := by
      by_contra hlt
      exact he (hc e.support (Nat.lt_of_not_ge hlt))
    rw [hEq, subsetExp_sum]
    exact hcard
  · exact absurd rfl he

lemma totalDegree_multilinearPoly_eq {n : ℕ} (c : Finset (Fin n) → ℝ) :
    (multilinearPoly c).totalDegree =
      (Finset.univ.filter (fun S : Finset (Fin n) => c S ≠ 0)).sup Finset.card := by
  apply le_antisymm
  · apply totalDegree_multilinearPoly_le
    intro S hS
    by_contra hne
    have hmem : S ∈ Finset.univ.filter (fun S : Finset (Fin n) => c S ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    exact absurd (Finset.le_sup (f := Finset.card) hmem) (Nat.not_le_of_gt hS)
  · rw [Finset.sup_le_iff]
    intro S hS
    have hne : c S ≠ 0 := (Finset.mem_filter.mp hS).2
    have hmem : subsetExp S ∈ (multilinearPoly c).support := by
      rw [MvPolynomial.mem_support_iff, coeff_multilinearPoly_subsetExp]
      exact hne
    have hle := MvPolynomial.le_totalDegree hmem
    simpa [subsetExp_sum] using hle

/-- Multilinearization of an arbitrary real multivariate polynomial `P`:
collects all monomial coefficients of `P` whose exponent support equals `S`. -/
noncomputable def multilinearCoeff {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (S : Finset (Fin n)) : ℝ :=
  ∑ e ∈ P.support.filter (fun e => e.support = S), P.coeff e

lemma eval_monomial_bool {n : ℕ} (e : Fin n →₀ ℕ) (a : ℝ) (x : Fin n → Bool) :
    MvPolynomial.eval (fun i => boolToReal (x i)) (MvPolynomial.monomial e a) =
      a * MvPolynomial.eval (fun i => boolToReal (x i)) (monomialPoly e.support) := by
  rw [MvPolynomial.eval_monomial, monomialPoly, map_prod]
  simp only [MvPolynomial.eval_X]
  congr 1
  rw [Finsupp.prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact boolToReal_pow (Finsupp.mem_support_iff.mp hi)

lemma eval_multilinearPoly_multilinearCoeff {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x : Fin n → Bool) :
    MvPolynomial.eval (fun i => boolToReal (x i)) (multilinearPoly (multilinearCoeff P)) =
      MvPolynomial.eval (fun i => boolToReal (x i)) P := by
  classical
  conv_rhs => rw [P.as_sum]
  rw [map_sum]
  simp_rw [eval_monomial_bool]
  rw [multilinearPoly, map_sum]
  simp_rw [map_mul, MvPolynomial.eval_C, multilinearCoeff, Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finsupp.support)
    (t := (Finset.univ : Finset (Finset (Fin n)))) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro e he
  rw [(Finset.mem_filter.mp he).2]

lemma multilinearCoeff_eq_zero_of_totalDegree_lt {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    {S : Finset (Fin n)} (hS : P.totalDegree < S.card) :
    multilinearCoeff P S = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  obtain ⟨heP, heS⟩ := Finset.mem_filter.mp he
  have h1 : S.card ≤ e.sum (fun _ k => k) := by
    rw [← heS, Finsupp.sum]
    calc e.support.card = ∑ _i ∈ e.support, 1 := by simp
      _ ≤ ∑ i ∈ e.support, e i := Finset.sum_le_sum (fun i hi =>
            Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
  have h2 : e.sum (fun _ k => k) ≤ P.totalDegree := MvPolynomial.le_totalDegree heP
  omega

/-- Alternating sum over subsets of a finite set `D`: equals `1` if `D = ∅` and `0` otherwise. -/
lemma sum_powerset_neg_one_pow {α : Type*} [DecidableEq α] (D : Finset α) :
    ∑ R ∈ D.powerset, (-1 : ℝ) ^ R.card = if D = ∅ then 1 else 0 := by
  by_cases hD : D = ∅
  · subst hD; simp
  · simp only [hD, ↓reduceIte]
    have h := Finset.sum_powerset_apply_card (x := D) (f := fun k => (-1 : ℝ) ^ k)
    have hzero : ((-1 : ℝ) + (1 : ℝ)) ^ D.card = 0 := by
      rw [neg_add_cancel, zero_pow (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hD))]
    rw [add_pow] at hzero
    simp only [one_pow, mul_one] at hzero
    rw [h]
    convert hzero using 1
    apply Finset.sum_congr rfl
    intro k _
    simp [nsmul_eq_mul, mul_comm]

lemma sum_powerset_neg_one_pow_sub {α : Type*} [DecidableEq α] (D : Finset α) :
    ∑ R ∈ D.powerset, (-1 : ℝ) ^ (D.card - R.card) = if D = ∅ then 1 else 0 := by
  have h := sum_powerset_neg_one_pow D
  rw [← h]
  apply Finset.sum_nbij (fun R => D \ R)
  · intro R _
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro R₁ hR₁ R₂ hR₂ hEq
    dsimp only at hEq
    have h1 : R₁ ⊆ D := Finset.mem_powerset.mp (Finset.mem_coe.mp hR₁)
    have h2 : R₂ ⊆ D := Finset.mem_powerset.mp (Finset.mem_coe.mp hR₂)
    rw [← Finset.sdiff_sdiff_eq_self h1, ← Finset.sdiff_sdiff_eq_self h2, hEq]
  · intro R hR
    refine ⟨D \ R, Finset.mem_coe.mpr (Finset.mem_powerset.mpr Finset.sdiff_subset), ?_⟩
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp (Finset.mem_coe.mp hR))
  · intro R hR
    rw [Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hR)]

/-- Exact integer Möbius coefficient of a Boolean function `f` at subset `S`. -/
def mobiusCoeff {n : ℕ} (f : BooleanFun n) (S : Finset (Fin n)) : ℤ :=
  ∑ T ∈ S.powerset, (-1 : ℤ) ^ (S.card - T.card) * boolToInt (f (indicator T))

/-- The Möbius degree of `f`: maximum cardinality of a subset with nonzero Möbius coefficient. -/
def mobiusDegree {n : ℕ} (f : BooleanFun n) : ℕ :=
  (Finset.univ.filter (fun S : Finset (Fin n) => mobiusCoeff f S ≠ 0)).sup Finset.card

/-- Möbius inversion on the Boolean lattice (forward direction):
recovering `c S` from subset sums `g T = ∑ U ⊆ T, c U`. -/
lemma mobius_inversion {n : ℕ} (c g : Finset (Fin n) → ℝ)
    (h : ∀ T : Finset (Fin n), ∑ U ∈ T.powerset, c U = g T) (S : Finset (Fin n)) :
    ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * g T = c S := by
  classical
  simp_rw [← h, Finset.mul_sum]
  calc ∑ T ∈ S.powerset, ∑ U ∈ T.powerset, (-1 : ℝ) ^ (S.card - T.card) * c U
      = ∑ T ∈ S.powerset, ∑ U ∈ S.powerset,
          if U ⊆ T then (-1 : ℝ) ^ (S.card - T.card) * c U else 0 := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext U
        simp only [Finset.mem_powerset, Finset.mem_filter]
        exact ⟨fun hUT => ⟨hUT.trans (Finset.mem_powerset.mp hT), hUT⟩, fun h => h.2⟩
    _ = ∑ U ∈ S.powerset, ∑ T ∈ S.powerset,
          if U ⊆ T then (-1 : ℝ) ^ (S.card - T.card) * c U else 0 := Finset.sum_comm
    _ = ∑ U ∈ S.powerset,
          (∑ T ∈ S.powerset.filter (fun T => U ⊆ T), (-1 : ℝ) ^ (S.card - T.card)) * c U := by
        apply Finset.sum_congr rfl
        intro U _
        rw [← Finset.sum_filter, Finset.sum_mul]
    _ = ∑ U ∈ S.powerset, (if S \ U = ∅ then (1 : ℝ) else 0) * c U := by
        apply Finset.sum_congr rfl
        intro U hU
        have hUS : U ⊆ S := Finset.mem_powerset.mp hU
        congr 1
        rw [← sum_powerset_neg_one_pow_sub (S \ U)]
        apply Finset.sum_nbij (fun T => T \ U)
        · intro T hT
          rw [Finset.mem_powerset]
          exact Finset.sdiff_subset_sdiff (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1)
            (Finset.Subset.refl U)
        · intro T₁ hT₁ T₂ hT₂ hEq
          dsimp only at hEq
          have h1 : U ⊆ T₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp hT₁)).2
          have h2 : U ⊆ T₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp hT₂)).2
          rw [← Finset.union_sdiff_of_subset h1, ← Finset.union_sdiff_of_subset h2, hEq]
        · intro R hR
          have hRsub : R ⊆ S \ U := Finset.mem_powerset.mp (Finset.mem_coe.mp hR)
          refine ⟨U ∪ R, ?_, ?_⟩
          · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
            exact ⟨Finset.union_subset hUS (hRsub.trans Finset.sdiff_subset),
              Finset.subset_union_left⟩
          · have hdisj : Disjoint R U := Finset.disjoint_of_subset_left hRsub Finset.sdiff_disjoint
            exact Finset.union_sdiff_cancel_left hdisj.symm
        · intro T hT
          have hTS : T ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
          have hUT : U ⊆ T := (Finset.mem_filter.mp hT).2
          have hcard : (S \ U).card - (T \ U).card = S.card - T.card := by
            rw [Finset.card_sdiff_of_subset hUS, Finset.card_sdiff_of_subset hUT]
            have := Finset.card_le_card hUT
            have := Finset.card_le_card hTS
            omega
          rw [hcard]
    _ = c S := by
        rw [Finset.sum_eq_single S]
        · simp
        · intro U hU hne
          have hUS : U ⊆ S := Finset.mem_powerset.mp hU
          have hsdiff : S \ U ≠ ∅ := by
            intro hemp
            have hSU : S ⊆ U := Finset.sdiff_eq_empty_iff_subset.mp hemp
            exact hne (Finset.Subset.antisymm hUS hSU)
          simp [hsdiff]
        · intro h; exact absurd (Finset.mem_powerset_self S) h

/-- Inverse Möbius identity on the Boolean lattice:
summing Möbius coefficients over subsets of `A` recovers `g A`. -/
lemma mobius_inverse {n : ℕ} (g : Finset (Fin n) → ℝ) (A : Finset (Fin n)) :
    ∑ S ∈ A.powerset, (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * g T) = g A := by
  classical
  calc ∑ S ∈ A.powerset, ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * g T
      = ∑ S ∈ A.powerset, ∑ T ∈ A.powerset,
          if T ⊆ S then (-1 : ℝ) ^ (S.card - T.card) * g T else 0 := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext T
        simp only [Finset.mem_powerset, Finset.mem_filter]
        exact ⟨fun hTS => ⟨hTS.trans (Finset.mem_powerset.mp hS), hTS⟩, fun h => h.2⟩
    _ = ∑ T ∈ A.powerset, ∑ S ∈ A.powerset,
          if T ⊆ S then (-1 : ℝ) ^ (S.card - T.card) * g T else 0 := Finset.sum_comm
    _ = ∑ T ∈ A.powerset,
          (∑ S ∈ A.powerset.filter (fun S => T ⊆ S), (-1 : ℝ) ^ (S.card - T.card)) * g T := by
        apply Finset.sum_congr rfl
        intro T _
        rw [← Finset.sum_filter, Finset.sum_mul]
    _ = ∑ T ∈ A.powerset, (if A \ T = ∅ then (1 : ℝ) else 0) * g T := by
        apply Finset.sum_congr rfl
        intro T hT
        have hTA : T ⊆ A := Finset.mem_powerset.mp hT
        congr 1
        rw [← sum_powerset_neg_one_pow (A \ T)]
        apply Finset.sum_nbij (fun S => S \ T)
        · intro S hS
          rw [Finset.mem_powerset]
          exact Finset.sdiff_subset_sdiff (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
            (Finset.Subset.refl T)
        · intro S₁ hS₁ S₂ hS₂ hEq
          dsimp only at hEq
          have h1 : T ⊆ S₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp hS₁)).2
          have h2 : T ⊆ S₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp hS₂)).2
          rw [← Finset.union_sdiff_of_subset h1, ← Finset.union_sdiff_of_subset h2, hEq]
        · intro R hR
          have hRsub : R ⊆ A \ T := Finset.mem_powerset.mp (Finset.mem_coe.mp hR)
          refine ⟨T ∪ R, ?_, ?_⟩
          · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
            exact ⟨Finset.union_subset hTA (hRsub.trans Finset.sdiff_subset),
              Finset.subset_union_left⟩
          · have hdisj : Disjoint R T := Finset.disjoint_of_subset_left hRsub Finset.sdiff_disjoint
            exact Finset.union_sdiff_cancel_left hdisj.symm
        · intro S hS
          rw [Finset.card_sdiff_of_subset (Finset.mem_filter.mp hS).2]
    _ = g A := by
        rw [Finset.sum_eq_single A]
        · simp
        · intro T hT hne
          have hTA : T ⊆ A := Finset.mem_powerset.mp hT
          have hsdiff : A \ T ≠ ∅ := by
            intro hemp
            exact hne (Finset.Subset.antisymm hTA (Finset.sdiff_eq_empty_iff_subset.mp hemp))
          simp [hsdiff]
        · intro h; exact absurd (Finset.mem_powerset_self A) h

/-- The canonical multilinear polynomial of `f` formed from its Möbius coefficients
represents `f` on `{0, 1}^n`. -/
theorem representsPoly_mobius {n : ℕ} (f : BooleanFun n) :
    RepresentsPoly (multilinearPoly (fun S => (mobiusCoeff f S : ℝ))) f := by
  intro x
  change MvPolynomial.eval (fun i => boolToReal (x i))
    (multilinearPoly (fun S => (mobiusCoeff f S : ℝ))) = boolToReal (f x)
  rw [eval_multilinearPoly]
  have hcast : ∀ S : Finset (Fin n), (mobiusCoeff f S : ℝ) =
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * boolToReal (f (indicator T)) := by
    intro S
    simp [mobiusCoeff, boolToReal_eq_cast]
  simp_rw [hcast]
  rw [mobius_inverse (fun T => boolToReal (f (indicator T))) (supportOf x), indicator_supportOf]

/-- Uniqueness of multilinear polynomial representation: any multilinear polynomial
representing `f` has coefficients equal to the Möbius coefficients of `f`. -/
theorem multilinear_coeff_unique {n : ℕ} {f : BooleanFun n} {c : Finset (Fin n) → ℝ}
    (hc : RepresentsPoly (multilinearPoly c) f) (S : Finset (Fin n)) :
    c S = (mobiusCoeff f S : ℝ) := by
  have hsum : ∀ T : Finset (Fin n), ∑ U ∈ T.powerset, c U = boolToReal (f (indicator T)) := by
    intro T
    have hT := hc (indicator T)
    change MvPolynomial.eval (fun i => boolToReal (indicator T i)) (multilinearPoly c) =
      boolToReal (f (indicator T)) at hT
    rw [eval_multilinearPoly, supportOf_indicator] at hT
    exact hT
  have hinv := mobius_inversion c (fun T => boolToReal (f (indicator T))) hsum S
  rw [← hinv]
  simp [mobiusCoeff, boolToReal_eq_cast]

/-- Every Boolean function admits a polynomial representation of degree `≤ mobiusDegree f`. -/
lemma exists_representsPoly {n : ℕ} (f : BooleanFun n) :
    ∃ P : MvPolynomial (Fin n) ℝ, RepresentsPoly P f ∧ P.totalDegree ≤ mobiusDegree f := by
  refine ⟨multilinearPoly (fun S => (mobiusCoeff f S : ℝ)), representsPoly_mobius f, ?_⟩
  apply totalDegree_multilinearPoly_le
  intro S hS
  have hzero : mobiusCoeff f S = 0 := by
    by_contra hne
    have hmem : S ∈ Finset.univ.filter (fun S : Finset (Fin n) => mobiusCoeff f S ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    exact absurd (Finset.le_sup (f := Finset.card) hmem) (Nat.not_le_of_gt hS)
  simp [hzero]

/-- Characterization of `polyDegree f ≤ d`: equivalent to existence of a real polynomial
representing `f` of total degree `≤ d`. -/
theorem polyDegree_le_iff {n : ℕ} {f : BooleanFun n} {d : ℕ} :
    polyDegree f ≤ d ↔
      ∃ P : MvPolynomial (Fin n) ℝ, RepresentsPoly P f ∧ P.totalDegree ≤ d := by
  constructor
  · intro hle
    have hne : { d : ℕ | ∃ P : MvPolynomial (Fin n) ℝ, RepresentsPoly P f ∧ P.totalDegree ≤ d }.Nonempty :=
      ⟨mobiusDegree f, exists_representsPoly f⟩
    obtain ⟨P, hrep, hdeg⟩ := Nat.sInf_mem hne
    exact ⟨P, hrep, hdeg.trans hle⟩
  · intro h
    exact Nat.sInf_le h

/-- Any polynomial `P` representing `f` has `multilinearCoeff P S = mobiusCoeff f S`. -/
theorem multilinearCoeff_eq_mobiusCoeff {n : ℕ} {f : BooleanFun n}
    {P : MvPolynomial (Fin n) ℝ} (hP : RepresentsPoly P f) (S : Finset (Fin n)) :
    multilinearCoeff P S = (mobiusCoeff f S : ℝ) := by
  apply multilinear_coeff_unique
  intro x
  change MvPolynomial.eval (fun i => boolToReal (x i)) (multilinearPoly (multilinearCoeff P)) =
    boolToReal (f x)
  rw [eval_multilinearPoly_multilinearCoeff]
  exact hP x

/-- Every Möbius coefficient of size strictly exceeding `polyDegree f` vanishes. -/
theorem mobiusCoeff_eq_zero_of_polyDegree_lt {n : ℕ} {f : BooleanFun n}
    {S : Finset (Fin n)} (hS : polyDegree f < S.card) :
    mobiusCoeff f S = 0 := by
  obtain ⟨P, hrep, hdeg⟩ := polyDegree_le_iff.mp (le_refl (polyDegree f))
  have h0 : multilinearCoeff P S = 0 :=
    multilinearCoeff_eq_zero_of_totalDegree_lt P (lt_of_le_of_lt hdeg hS)
  rw [multilinearCoeff_eq_mobiusCoeff hrep S] at h0
  exact Int.cast_eq_zero.mp h0

/-- **Degree Equivalence Theorem**: `polyDegree f = mobiusDegree f`. -/
theorem polyDegree_eq_mobiusDegree {n : ℕ} (f : BooleanFun n) :
    polyDegree f = mobiusDegree f := by
  apply le_antisymm
  · exact polyDegree_le_iff.mpr (exists_representsPoly f)
  · rw [mobiusDegree, Finset.sup_le_iff]
    intro S hS
    have hne : mobiusCoeff f S ≠ 0 := (Finset.mem_filter.mp hS).2
    by_contra hgt
    exact hne (mobiusCoeff_eq_zero_of_polyDegree_lt (Nat.lt_of_not_ge hgt))

/-- Upper bound on `polyDegree f` from a multilinear coefficient function `c`. -/
theorem polyDegree_le_of_multilinear {n : ℕ} {f : BooleanFun n} {c : Finset (Fin n) → ℝ} {d : ℕ}
    (hrep : RepresentsPoly (multilinearPoly c) f)
    (hdeg : ∀ S : Finset (Fin n), d < S.card → c S = 0) :
    polyDegree f ≤ d :=
  polyDegree_le_iff.mpr ⟨multilinearPoly c, hrep, totalDegree_multilinearPoly_le c d hdeg⟩

/-- Exact computation of `polyDegree f` from a multilinear representation `c`. -/
theorem polyDegree_eq_of_multilinear {n : ℕ} {f : BooleanFun n} {c : Finset (Fin n) → ℝ} {d : ℕ}
    (hrep : RepresentsPoly (multilinearPoly c) f)
    (hdeg : ∀ S : Finset (Fin n), d < S.card → c S = 0)
    (hwit : ∃ S : Finset (Fin n), S.card = d ∧ c S ≠ 0) :
    polyDegree f = d := by
  apply le_antisymm
  · exact polyDegree_le_of_multilinear hrep hdeg
  · obtain ⟨S, hScard, hSne⟩ := hwit
    by_contra hlt
    have h0 := mobiusCoeff_eq_zero_of_polyDegree_lt (f := f) (S := S)
      (by omega : polyDegree f < S.card)
    have heq := multilinear_coeff_unique hrep S
    rw [h0, Int.cast_zero] at heq
    exact hSne heq

/-- Degree `0` functions are constant. -/
theorem polyDegree_eq_zero_iff {n : ℕ} (f : BooleanFun n) :
    polyDegree f = 0 ↔ ∀ x y : Fin n → Bool, f x = f y := by
  constructor
  · intro h0 x y
    obtain ⟨P, hrep, hdeg⟩ := polyDegree_le_iff.mp (le_of_eq h0)
    have hP : P = MvPolynomial.C (P.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hdeg)
    have hx := hrep x
    have hy := hrep y
    rw [hP, MvPolynomial.eval_C] at hx hy
    have heq : (if f x then (1 : ℝ) else 0) = if f y then 1 else 0 := hx.symm.trans hy
    cases hfx : f x <;> cases hfy : f y <;> simp [hfx, hfy] at heq ⊢
  · intro hconst
    rw [← Nat.le_zero, polyDegree_le_iff]
    refine ⟨MvPolynomial.C (boolToReal (f (fun _ => false))), ?_, ?_⟩
    · intro x
      simp [boolToReal, hconst x (fun _ => false)]
    · simp

/-- `polyDegree f ≤ n` for every `n`-bit Boolean function `f`. -/
theorem polyDegree_le_dim {n : ℕ} (f : BooleanFun n) : polyDegree f ≤ n := by
  rw [polyDegree_eq_mobiusDegree, mobiusDegree, Finset.sup_le_iff]
  intro S _
  simpa using Finset.card_le_univ S

end DegreeSensitivity
