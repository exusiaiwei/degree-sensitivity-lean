module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Advertised Statements: Degree–Sensitivity Exponent (Tao's Constant #37a)

This is the small, self-contained trusted statement surface audited by a human reader.
All definitions use standard Mathlib primitives (`Fin`, `Finset`, `MvPolynomial`,
`Real.log`, `sInf`), and every advertised theorem below is proved without `sorry`
in `Solution.lean`.
-/

namespace DegreeSensitivity

/-- A Boolean function on `n` input bits `x : Fin n → Bool`. -/
abbrev BooleanFun (n : ℕ) := (Fin n → Bool) → Bool

/-- Flip the `i`-th input bit of `x : Fin n → Bool`. -/
def flipBit {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  fun j => if j = i then !x j else x j

/-- The sensitivity `s(f, x)` of a Boolean function `f` at input `x`:
the number of coordinates `i : Fin n` such that flipping bit `i` changes `f x`. -/
def sensitivityAt {n : ℕ} (f : BooleanFun n) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => f (flipBit x i) ≠ f x)).card

/-- The maximum sensitivity `s(f) = max_x s(f, x)` of a Boolean function `f`. -/
def maxSensitivity {n : ℕ} (f : BooleanFun n) : ℕ :=
  Finset.univ.sup (sensitivityAt f)

/-- A real multivariate polynomial `P ∈ ℝ[x₀, ..., x_{n-1}]` represents a Boolean
function `f : {0, 1}^n → {0, 1}` if evaluating `P` at `(if x i then 1 else 0)`
equals `(if f x then 1 else 0)` for every `x : Fin n → Bool`. -/
def RepresentsPoly {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (f : BooleanFun n) : Prop :=
  ∀ x : Fin n → Bool,
    MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) P = if f x then 1 else 0

/-- The exact real polynomial degree `deg(f)` of a Boolean function `f`:
the minimum total degree of a real multivariate polynomial representing `f` on `{0, 1}^n`. -/
noncomputable def polyDegree {n : ℕ} (f : BooleanFun n) : ℕ :=
  sInf { d : ℕ | ∃ P : MvPolynomial (Fin n) ℝ, RepresentsPoly P f ∧ P.totalDegree ≤ d }

/-- Tao's Optimization Constant #37a (the degree–sensitivity exponent `C_37`):
the infimum of all real exponents `α` for which `s(f) = O(deg(f)^α)` holds uniformly
over all nonconstant Boolean functions `f`. -/
noncomputable def degSensitivityExponent : ℝ :=
  sInf { α : ℝ | ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : BooleanFun n),
    1 ≤ polyDegree f → (maxSensitivity f : ℝ) ≤ C * (polyDegree f : ℝ) ^ α }

/-- Witness `(n = 3, deg = 2, s = 3)` given by the 3-bit Not-All-Equal function `NAE₃`. -/
theorem nae3_witness :
    ∃ f : BooleanFun 3, polyDegree f = 2 ∧ maxSensitivity f = 3 := by
  sorry

/-- Kushilevitz's `(n = 6, deg = 3, s = 6)` witness, achieving `log 6 / log 3 ≈ 1.63093`. -/
theorem kushilevitz_witness :
    ∃ f : BooleanFun 6, polyDegree f = 3 ∧ maxSensitivity f = 6 := by
  sorry

/-- Composed witness `(n = 9, deg = 4, s = 9)` given by `NAE₃ ∘ NAE₃`. -/
theorem nae3_comp_nae3_witness :
    ∃ f : BooleanFun 9, polyDegree f = 4 ∧ maxSensitivity f = 9 := by
  sorry

/-- Explicit `(n = 13, deg = 5, s = 13)` witness obtained via weighted-degree-5
composition of a 9-bit outer function with two copies of `NAE₃`. -/
theorem deg5_sens13_witness :
    ∃ f : BooleanFun 13, polyDegree f = 5 ∧ maxSensitivity f = 13 := by
  sorry

/-- Asymptotic lower bound on Tao's Constant #37a from Kushilevitz's function and
iterated Boolean function composition: `C_37 ≥ log 6 / log 3`. -/
theorem kushilevitz_exponent_lower_bound :
    Real.log 6 / Real.log 3 ≤ degSensitivityExponent := by
  sorry

/-- Sharp upper bound for degree 2: every Boolean function of real degree `≤ 2`
has maximum sensitivity `≤ 3` (impossibility of `(n = 4, d = 2)`). -/
theorem maxSensitivity_le_three_of_deg_le_two :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 2 → maxSensitivity f ≤ 3 := by
  sorry

/-- Sharp upper bound for degree 3: every Boolean function of real degree `≤ 3`
has maximum sensitivity `≤ 6` (impossibility of `(n = 7, d = 3)`). -/
theorem maxSensitivity_le_six_of_deg_le_three :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 3 → maxSensitivity f ≤ 6 := by
  sorry

/-- Sharp upper bound for degree 4: every Boolean function of real degree `≤ 4`
has maximum sensitivity `≤ 9` (impossibility of `(n = 10, d = 4)`, matching `NAE₃ ∘ NAE₃`). -/
theorem maxSensitivity_le_nine_of_deg_le_four :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 4 → maxSensitivity f ≤ 9 := by
  sorry

/-- Sharpened upper bound for degree 5: every Boolean function of real degree `≤ 5`
has maximum sensitivity `≤ 14` (impossibility of `(n = 15, d = 5)`, improving Wellens 2022 `15`). -/
theorem maxSensitivity_le_fourteen_of_deg_le_five :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 5 → maxSensitivity f ≤ 14 := by
  sorry

/-- Sharpened upper bound for degree 6: every Boolean function of real degree `≤ 6`
has maximum sensitivity `≤ 20` (impossibility of `(n = 21, d = 6)`, improving Wellens 2022 `21`). -/
theorem maxSensitivity_le_twenty_of_deg_le_six :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 6 → maxSensitivity f ≤ 20 := by
  sorry

/-- Sharpened upper bound for degree 7: every Boolean function of real degree `≤ 7`
has maximum sensitivity `≤ 28` (impossibility of `(n = 29, d = 7)`, improving Wellens 2022 `29`). -/
theorem maxSensitivity_le_twentyeight_of_deg_le_seven :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 7 → maxSensitivity f ≤ 28 := by
  sorry

/-- Sharpened upper bound for degree 8: every Boolean function of real degree `≤ 8`
has maximum sensitivity `≤ 36` (impossibility of `(n = 37, d = 8)`, improving Wellens 2022 `38`). -/
theorem maxSensitivity_le_thirtysix_of_deg_le_eight :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 8 → maxSensitivity f ≤ 36 := by
  sorry

/-- Sharpened upper bound for degree 9: every Boolean function of real degree `≤ 9`
has maximum sensitivity `≤ 46` (impossibility of `(n = 47, d = 9)`, improving Wellens 2022 `47`). -/
theorem maxSensitivity_le_fortysix_of_deg_le_nine :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 9 → maxSensitivity f ≤ 46 := by
  sorry

end DegreeSensitivity
