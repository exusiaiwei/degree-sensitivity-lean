module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Core Definitions for the Degree–Sensitivity Problem (Tao's Constant #37a)

This module defines Boolean functions `f : {0, 1}^n → {0, 1}`, pointwise and maximum
sensitivity `s(f)`, exact real polynomial representation and degree `deg(f)`, and
the degree–sensitivity exponent `C_37`.

The definitions in this file are kept strictly identical to those in `Challenge.lean`,
as verified mechanically by `lake comparator`.
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

end DegreeSensitivity
