module

public import DegreeSensitivity.Multilinear
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
# Sensitivity Properties and Subcube Restriction

Basic properties of `flipBit`, `sensitivityAt`, and `maxSensitivity`, together with
invariance of `polyDegree` under negation and affine input transformations, and the
Subcube Restriction Theorem: any Boolean function `f` with `maxSensitivity f ≥ k`
restricts to a normalized `k`-bit Boolean function `g` with `polyDegree g ≤ polyDegree f`,
`g 0 = false`, and `g (e_i) = true` for all `i : Fin k`.
-/

namespace DegreeSensitivity

open scoped BigOperators
open MvPolynomial

/-- The all-false bitstring `0 ∈ {0, 1}^n`. -/
def zeroVec (n : ℕ) : Fin n → Bool := fun _ => false

/-- The `i`-th standard basis vector `e_i ∈ {0, 1}^n`. -/
def basisVec {n : ℕ} (i : Fin n) : Fin n → Bool := flipBit (zeroVec n) i

@[simp] lemma flipBit_self {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    flipBit x i i = !x i := by
  simp [flipBit]

@[simp] lemma flipBit_ne {n : ℕ} (x : Fin n → Bool) {i j : Fin n} (h : j ≠ i) :
    flipBit x i j = x j := by
  simp [flipBit, h]

@[simp] lemma flipBit_involutive {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    flipBit (flipBit x i) i = x := by
  funext j
  by_cases h : j = i
  · subst h; simp [flipBit]
  · simp [flipBit, h]

lemma basisVec_apply {n : ℕ} (i j : Fin n) :
    basisVec i j = decide (j = i) := by
  by_cases h : j = i <;> simp [basisVec, flipBit, zeroVec, h]

lemma sensitivityAt_le {n : ℕ} (f : BooleanFun n) (x : Fin n → Bool) :
    sensitivityAt f x ≤ n := by
  simpa [sensitivityAt] using
    Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => f (flipBit x i) ≠ f x)

lemma maxSensitivity_le {n : ℕ} (f : BooleanFun n) : maxSensitivity f ≤ n := by
  rw [maxSensitivity, Finset.sup_le_iff]
  intro x _
  exact sensitivityAt_le f x

lemma sensitivityAt_le_maxSensitivity {n : ℕ} (f : BooleanFun n) (x : Fin n → Bool) :
    sensitivityAt f x ≤ maxSensitivity f :=
  Finset.le_sup (f := sensitivityAt f) (Finset.mem_univ x)

/-- If `f 0 = false` and `f (e_i) = true` for all `i : Fin n`, then `s(f, 0) = n` and `s(f) = n`. -/
theorem sensitivityAt_zero_eq_dim {n : ℕ} {f : BooleanFun n}
    (h0 : f (zeroVec n) = false) (h1 : ∀ i : Fin n, f (basisVec i) = true) :
    sensitivityAt f (zeroVec n) = n := by
  rw [sensitivityAt]
  have hfilt : Finset.univ.filter (fun i : Fin n => f (flipBit (zeroVec n) i) ≠ f (zeroVec n)) =
      Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    change f (basisVec i) ≠ f (zeroVec n)
    rw [h0, h1 i]
    decide
  rw [hfilt]
  simp

theorem maxSensitivity_eq_dim_of_normalized {n : ℕ} {f : BooleanFun n}
    (h0 : f (zeroVec n) = false) (h1 : ∀ i : Fin n, f (basisVec i) = true) :
    maxSensitivity f = n := by
  apply le_antisymm (maxSensitivity_le f)
  calc n = sensitivityAt f (zeroVec n) := (sensitivityAt_zero_eq_dim h0 h1).symm
    _ ≤ maxSensitivity f := sensitivityAt_le_maxSensitivity f (zeroVec n)

/-- There exists an input `x : Fin n → Bool` achieving `maxSensitivity f`. -/
theorem exists_sensitivityAt_eq_maxSensitivity {n : ℕ} (f : BooleanFun n) :
    ∃ x : Fin n → Bool, sensitivityAt f x = maxSensitivity f := by
  have hne : (Finset.univ : Finset (Fin n → Bool)).Nonempty :=
    ⟨zeroVec n, Finset.mem_univ _⟩
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup Finset.univ hne (sensitivityAt f)
  exact ⟨x, hx.symm⟩

/-- For any degree-0 (constant) Boolean function, `maxSensitivity f = 0`. -/
theorem maxSensitivity_eq_zero_of_polyDegree_zero {n : ℕ} {f : BooleanFun n}
    (h0 : polyDegree f = 0) : maxSensitivity f = 0 := by
  have hconst := (polyDegree_eq_zero_iff f).mp h0
  rw [maxSensitivity, ← Nat.le_zero, Finset.sup_le_iff]
  intro x _
  rw [sensitivityAt, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  simp [hconst (flipBit x i) x]

/-- General total-degree bound for polynomial substitution `MvPolynomial.aeval φ P`:
if every substituted polynomial `φ j` has total degree `≤ k`, then
`(aeval φ P).totalDegree ≤ k * P.totalDegree`. -/
theorem totalDegree_aeval_le_mul {n m : ℕ} (φ : Fin n → MvPolynomial (Fin m) ℝ)
    (P : MvPolynomial (Fin n) ℝ) (k : ℕ) (hφ : ∀ j, (φ j).totalDegree ≤ k) :
    (MvPolynomial.aeval φ P).totalDegree ≤ k * P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  rw [Finset.sup_le_iff]
  intro e he
  rw [MvPolynomial.aeval_monomial]
  change (MvPolynomial.C (P.coeff e) * e.prod (fun j r => (φ j) ^ r)).totalDegree ≤ _
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ j ∈ e.support, ((φ j) ^ (e j)).totalDegree
      ≤ ∑ j ∈ e.support, e j * (φ j).totalDegree :=
        Finset.sum_le_sum (fun j _ => MvPolynomial.totalDegree_pow (φ j) (e j))
    _ ≤ ∑ j ∈ e.support, e j * k :=
        Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left (e j) (hφ j))
    _ = (∑ j ∈ e.support, e j) * k := (Finset.sum_mul _ _ _).symm
    _ = k * e.sum (fun _ r => r) := by rw [Finsupp.sum, mul_comm]
    _ ≤ k * P.totalDegree := Nat.mul_le_mul_left k (MvPolynomial.le_totalDegree he)

/-- Specialization to degree `≤ 1` substitutions: `(aeval φ P).totalDegree ≤ P.totalDegree`. -/
theorem totalDegree_aeval_le {n m : ℕ} (φ : Fin n → MvPolynomial (Fin m) ℝ)
    (P : MvPolynomial (Fin n) ℝ) (hφ : ∀ j, (φ j).totalDegree ≤ 1) :
    (MvPolynomial.aeval φ P).totalDegree ≤ P.totalDegree := by
  simpa using totalDegree_aeval_le_mul φ P 1 hφ

/-- Evaluation of `MvPolynomial.aeval φ P` at `v` equals evaluation of `P` at `eval v ∘ φ`. -/
lemma eval_aeval_eq {n m : ℕ} (φ : Fin n → MvPolynomial (Fin m) ℝ)
    (P : MvPolynomial (Fin n) ℝ) (v : Fin m → ℝ) :
    MvPolynomial.eval v (MvPolynomial.aeval φ P) =
      MvPolynomial.eval (fun j => MvPolynomial.eval v (φ j)) P := by
  change (MvPolynomial.eval v).comp (MvPolynomial.aeval φ).toRingHom P =
    MvPolynomial.eval (fun j => MvPolynomial.eval v (φ j)) P
  have hring : (MvPolynomial.eval v).comp (MvPolynomial.aeval φ).toRingHom =
      MvPolynomial.eval (fun j => MvPolynomial.eval v (φ j)) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro j; simp
  exact RingHom.congr_fun hring P

lemma totalDegree_neg_le {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    (-P).totalDegree ≤ P.totalDegree := by
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro e he
  have hmem : e ∈ P.support := by
    rw [MvPolynomial.mem_support_iff] at he ⊢
    simpa [Finsupp.neg_apply] using he
  exact MvPolynomial.le_totalDegree hmem

/-- Output negation preserves `polyDegree`. -/
theorem polyDegree_not {n : ℕ} (f : BooleanFun n) :
    polyDegree (fun x => !f x) = polyDegree f := by
  have hle : ∀ g : BooleanFun n, polyDegree (fun x => !g x) ≤ polyDegree g := by
    intro g
    rw [polyDegree_le_iff]
    obtain ⟨P, hrep, hdeg⟩ := polyDegree_le_iff.mp (le_refl (polyDegree g))
    refine ⟨1 - P, ?_, ?_⟩
    · intro x
      have hx := hrep x
      simp only [map_sub, map_one, hx]
      rcases Bool.eq_false_or_eq_true (g x) with hgx | hgx <;> simp [hgx]
    · rw [sub_eq_add_neg]
      refine (MvPolynomial.totalDegree_add 1 (-P)).trans ?_
      rw [MvPolynomial.totalDegree_one]
      exact max_le (Nat.zero_le _) ((totalDegree_neg_le P).trans hdeg)
  apply le_antisymm (hle f)
  have h2 := hle (fun x => !f x)
  simpa [Bool.not_not] using h2

/-- Helper: total degree of `1 - X i` is `≤ 1`. -/
lemma totalDegree_one_sub_X {m : ℕ} (i : Fin m) :
    (1 - MvPolynomial.X i : MvPolynomial (Fin m) ℝ).totalDegree ≤ 1 := by
  rw [sub_eq_add_neg]
  refine (MvPolynomial.totalDegree_add 1 (-MvPolynomial.X i)).trans ?_
  rw [MvPolynomial.totalDegree_one]
  exact max_le (Nat.zero_le _) ((totalDegree_neg_le _).trans (by simp [MvPolynomial.totalDegree_X]))

/-- **Subcube Restriction Theorem**:
If `f : BooleanFun n` has `k ≤ maxSensitivity f`, then there exists a normalized
`k`-bit Boolean function `g : BooleanFun k` such that:
1. `polyDegree g ≤ polyDegree f`,
2. `g (zeroVec k) = false`, and
3. `∀ i : Fin k, g (basisVec i) = true`. -/
theorem exists_normalized_subfunction {n k : ℕ} (f : BooleanFun n)
    (hk : k ≤ maxSensitivity f) :
    ∃ g : BooleanFun k,
      polyDegree g ≤ polyDegree f ∧
      g (zeroVec k) = false ∧
      ∀ i : Fin k, g (basisVec i) = true := by
  classical
  obtain ⟨x, hx⟩ := exists_sensitivityAt_eq_maxSensitivity f
  let S : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => f (flipBit x j) ≠ f x)
  have hcard : k ≤ S.card := by
    rw [← hx] at hk
    exact hk
  -- Choose an injection `emb : Fin k ↪ Fin n` landing inside `S`.
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hcard
  let eT : Fin k ≃ T := (Fintype.equivFinOfCardEq (by simp [hTcard])).symm
  let emb : Fin k → Fin n := fun i => (eT i).1
  have hemb_inj : Function.Injective emb := by
    intro i₁ i₂ h
    exact eT.injective (Subtype.ext h)
  have hemb_mem : ∀ i : Fin k, emb i ∈ S := fun i => hTS (eT i).2
  -- Define the coordinate map `{0, 1}^k → {0, 1}^n` embedding the sensitive subcube centered at `x`.
  let embed : (Fin k → Bool) → (Fin n → Bool) := fun y j =>
    if h : ∃ i : Fin k, emb i = j then Bool.xor (x j) (y h.choose) else x j
  have hembed_emb : ∀ (y : Fin k → Bool) (i : Fin k), embed y (emb i) = Bool.xor (x (emb i)) (y i) := by
    intro y i
    have hex : ∃ i' : Fin k, emb i' = emb i := ⟨i, rfl⟩
    simp only [embed, hex, ↓reduceDIte]
    congr 2
    exact hemb_inj hex.choose_spec
  have hembed_zero : embed (zeroVec k) = x := by
    funext j
    by_cases h : ∃ i : Fin k, emb i = j
    · simp [embed, h, zeroVec]
    · simp [embed, h]
  have hembed_basis : ∀ i : Fin k, embed (basisVec i) = flipBit x (emb i) := by
    intro i
    funext j
    by_cases hji : j = emb i
    · subst hji
      rw [hembed_emb, basisVec_apply, flipBit_self]
      cases x (emb i) <;> simp
    · rw [flipBit_ne _ hji]
      by_cases h : ∃ i' : Fin k, emb i' = j
      · simp only [embed, h, ↓reduceDIte]
        have hne : h.choose ≠ i := by
          intro heq
          apply hji
          rw [← h.choose_spec, heq]
        rw [basisVec_apply, decide_eq_false hne]
        cases x j <;> rfl
      · simp [embed, h]
  -- Define `g y = xor (f (embed y)) (f x)`.
  let g : BooleanFun k := fun y => Bool.xor (f (embed y)) (f x)
  refine ⟨g, ?_, ?_, ?_⟩
  · -- Degree bound: `polyDegree g ≤ polyDegree f`
    -- First show `polyDegree (fun y => f (embed y)) ≤ polyDegree f`.
    have hdeg_raw : polyDegree (fun y => f (embed y)) ≤ polyDegree f := by
      rw [polyDegree_le_iff]
      obtain ⟨P, hrep, hPdeg⟩ := polyDegree_le_iff.mp (le_refl (polyDegree f))
      let φ : Fin n → MvPolynomial (Fin k) ℝ := fun j =>
        if h : ∃ i : Fin k, emb i = j then
          if x j then 1 - MvPolynomial.X h.choose else MvPolynomial.X h.choose
        else MvPolynomial.C (boolToReal (x j))
      refine ⟨MvPolynomial.aeval φ P, ?_, ?_⟩
      · intro y
        change MvPolynomial.eval (fun i => boolToReal (y i)) (MvPolynomial.aeval φ P) =
          boolToReal (f (embed y))
        rw [eval_aeval_eq]
        have harg : (fun j => MvPolynomial.eval (fun i => boolToReal (y i)) (φ j)) =
            (fun j => boolToReal (embed y j)) := by
          funext j
          by_cases h : ∃ i : Fin k, emb i = j
          · simp only [φ, embed, h, ↓reduceDIte]
            cases hxj : x j <;> cases hy : y h.choose <;> simp [boolToReal, hy]
          · simp [φ, embed, h]
        rw [harg]
        exact hrep (embed y)
      · refine (totalDegree_aeval_le φ P ?_).trans hPdeg
        intro j
        by_cases h : ∃ i : Fin k, emb i = j
        · simp only [φ, h, ↓reduceDIte]
          cases x j
          · simp [MvPolynomial.totalDegree_X]
          · exact totalDegree_one_sub_X h.choose
        · simp [φ, h]
    cases hfx : f x
    · have hg : g = fun y => f (embed y) := by
        funext y; simp [g, hfx]
      rw [hg]
      exact hdeg_raw
    · have hg : g = fun y => !(f (embed y)) := by
        funext y; simp [g, hfx]
      rw [hg, polyDegree_not]
      exact hdeg_raw
  · -- `g (zeroVec k) = false`
    simp [g, hembed_zero]
  · -- `∀ i, g (basisVec i) = true`
    intro i
    simp only [g, hembed_basis i]
    have hmem : emb i ∈ S := hemb_mem i
    have hne : f (flipBit x (emb i)) ≠ f x := (Finset.mem_filter.mp hmem).2
    cases h1 : f (flipBit x (emb i)) <;> cases h2 : f x <;> simp_all

/-- Contrapositive form of Subcube Restriction: if no normalized `k`-bit Boolean function
of degree `≤ d` exists, then every Boolean function of degree `≤ d` has `maxSensitivity f < k`. -/
theorem maxSensitivity_lt_of_no_normalized {k d : ℕ}
    (hno : ¬ ∃ g : BooleanFun k, polyDegree g ≤ d ∧ g (zeroVec k) = false ∧
      ∀ i : Fin k, g (basisVec i) = true) :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ d → maxSensitivity f < k := by
  intro n f hf
  by_contra hge
  obtain ⟨g, hgdeg, hg0, hg1⟩ := exists_normalized_subfunction f (Nat.le_of_not_lt hge)
  exact hno ⟨g, hgdeg.trans hf, hg0, hg1⟩

/-- Every Boolean function of degree `≤ 1` has `maxSensitivity f ≤ 1`.
(Direct elementary proof via Möbius coefficients of size 1!) -/
theorem maxSensitivity_le_one_of_deg_le_one :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 1 → maxSensitivity f ≤ 1 := by
  intro n f hf
  suffices hno : ¬ ∃ g : BooleanFun 2, polyDegree g ≤ 1 ∧ g (zeroVec 2) = false ∧
      ∀ i : Fin 2, g (basisVec i) = true by
    have := maxSensitivity_lt_of_no_normalized hno n f hf
    omega
  rintro ⟨g, hgdeg, hg0, hg1⟩
  have h2 : mobiusCoeff g Finset.univ = 0 :=
    mobiusCoeff_eq_zero_of_polyDegree_lt (by simpa using Nat.lt_of_le_of_lt hgdeg (by decide : 1 < 2))
  -- Evaluate `g (fun _ => true)` via the degree-1 multilinear expansion.
  have hrep := representsPoly_mobius g
  have hval0 := multilinear_coeff_unique hrep ∅
  have hval := hrep (fun _ => true)
  change MvPolynomial.eval (fun _ => (1 : ℝ))
    (multilinearPoly (fun S => (mobiusCoeff g S : ℝ))) = boolToReal (g (fun _ => true)) at hval
  have hsum : ∑ S : Finset (Fin 2), (mobiusCoeff g S : ℝ) = boolToReal (g (fun _ => true)) := by
    have hsupp : supportOf (fun _ : Fin 2 => true) = Finset.univ := by ext i; simp
    have hE := eval_multilinearPoly (fun S => (mobiusCoeff g S : ℝ)) (fun _ => true)
    rw [hsupp, Finset.powerset_univ] at hE
    simpa [boolToReal] using hE.symm.trans hval
  have hind0 : indicator (∅ : Finset (Fin 2)) = zeroVec 2 := by funext j; simp [indicator, zeroVec]
  have hm0 : mobiusCoeff g ∅ = 0 := by
    simp [mobiusCoeff, hind0, hg0]
  have hm_s : ∀ i : Fin 2, mobiusCoeff g {i} = 1 := by
    intro i
    have hpow : ({i} : Finset (Fin 2)).powerset = {∅, {i}} := by
      ext T; simp [Finset.subset_singleton_iff]
    rw [mobiusCoeff, hpow, Finset.sum_pair (by simp)]
    have hind1 : indicator ({i} : Finset (Fin 2)) = basisVec i := by
      funext j; simp [indicator, basisVec_apply]
    simp [hind0, hind1, hg0, hg1 i]
  have huniv : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, Finset.univ} := by
    decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hsum
  simp only [hm0, hm_s 0, hm_s 1, h2, Int.cast_zero, Int.cast_one] at hsum
  rcases Bool.eq_false_or_eq_true (g (fun _ => true)) with hgt | hgt <;>
    simp [hgt, boolToReal] at hsum

end DegreeSensitivity
