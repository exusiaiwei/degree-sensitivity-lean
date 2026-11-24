module

public import DegreeSensitivity.Composition
public import DegreeSensitivity.Deg4Sharp
public import DegreeSensitivity.WitnessEngine

@[expose] public section

/-!
# Explicit Boolean Function Witnesses

Pure kernel-verified witnesses (zero `sorry`, zero `native_decide`, standard axioms only):
- `nae3_witness_proof`: `(n = 3, deg = 2, s = 3)` (`NAE₃`)
- `kushilevitz_witness_proof`: `(n = 6, deg = 3, s = 6)` (Kushilevitz's 6-bit function)
- `nae3_comp_nae3_witness_proof`: `(n = 9, deg = 4, s = 9)` (`NAE₃ ∘ NAE₃`)
- `deg5_sens13_witness_proof`: `(n = 13, deg = 5, s = 13)` via weighted-degree-5
  composition of a 9-bit outer function `outerG9` with two copies of `NAE₃`
- `kushilevitz_exponent_lower_bound_proof`: `Real.log 6 / Real.log 3 ≤ degSensitivityExponent`
-/

namespace DegreeSensitivity

def bt2 (a b c d : Bool) : BoolTree 2 :=
  .node (.node (.leaf a) (.leaf b)) (.node (.leaf c) (.leaf d))

def bt4 (a b c d : BoolTree 2) : BoolTree 4 :=
  .node (.node a b) (.node c d)

/-- Truth tree for `NAE₃` (`n = 3, deg = 2, s = 3`). -/
def nae3Tree : BoolTree 3 :=
  .node (bt2 false true true true) (bt2 true true true false)

/-- The 3-bit Not-All-Equal function `NAE₃`. -/
def nae3Fun : BooleanFun 3 := nae3Tree.eval

lemma nae3Fun_deg_le : polyDegree nae3Fun ≤ 2 :=
  polyDegree_le_of_checkDeg nae3Tree (by decide)

lemma nae3Fun_normalized :
    nae3Fun (zeroVec 3) = false ∧ ∀ i : Fin 3, nae3Fun (basisVec i) = true :=
  nae3Tree.normalized_of_check (by decide)

theorem nae3_witness_proof :
    ∃ f : BooleanFun 3, polyDegree f = 2 ∧ maxSensitivity f = 3 := by
  refine ⟨nae3Fun, ?_, ?_⟩
  · have hle : polyDegree nae3Fun ≤ 2 := nae3Fun_deg_le
    have hsens : maxSensitivity nae3Fun = 3 :=
      maxSensitivity_eq_dim_of_normalized nae3Fun_normalized.1 nae3Fun_normalized.2
    have hgt1 : ¬ polyDegree nae3Fun ≤ 1 := by
      intro h1
      have := maxSensitivity_le_one_of_deg_le_one 3 nae3Fun h1
      omega
    omega
  · exact maxSensitivity_eq_dim_of_normalized nae3Fun_normalized.1 nae3Fun_normalized.2

/-- Truth tree for Kushilevitz's 6-bit degree-3 function (`n = 6, deg = 3, s = 6`). -/
def kushilevitzTree : BoolTree 6 :=
  (.node
    (.node
      (bt4 (bt2 false true true true) (bt2 true true true false) (bt2 true true true false) (bt2 true true true false))
      (bt4 (bt2 true true true true) (bt2 true false true false) (bt2 true true false false) (bt2 false false false false)))
    (.node
      (bt4 (bt2 true true true true) (bt2 true true false false) (bt2 true false true false) (bt2 false false false false))
      (bt4 (bt2 true false false false) (bt2 true false false false) (bt2 true false false false) (bt2 false false false true))))

/-- Kushilevitz's 6-bit Boolean function (`deg = 3, s = 6`). -/
def kushilevitzFun : BooleanFun 6 := kushilevitzTree.eval

lemma kushilevitzFun_deg_le : polyDegree kushilevitzFun ≤ 3 :=
  polyDegree_le_of_checkDeg kushilevitzTree (by decide)

lemma kushilevitzFun_normalized :
    kushilevitzFun (zeroVec 6) = false ∧ ∀ i : Fin 6, kushilevitzFun (basisVec i) = true :=
  kushilevitzTree.normalized_of_check (by decide)

theorem kushilevitz_witness_proof :
    ∃ f : BooleanFun 6, polyDegree f = 3 ∧ maxSensitivity f = 6 := by
  refine ⟨kushilevitzFun, ?_, ?_⟩
  · have hle : polyDegree kushilevitzFun ≤ 3 := kushilevitzFun_deg_le
    have hsens : maxSensitivity kushilevitzFun = 6 :=
      maxSensitivity_eq_dim_of_normalized kushilevitzFun_normalized.1 kushilevitzFun_normalized.2
    have hgt2 : ¬ polyDegree kushilevitzFun ≤ 2 := by
      intro h2
      have := maxSensitivity_le_three_of_deg_le_two_proof 6 kushilevitzFun h2
      omega
    omega
  · exact maxSensitivity_eq_dim_of_normalized kushilevitzFun_normalized.1 kushilevitzFun_normalized.2

/-- Asymptotic lower bound `Real.log 6 / Real.log 3 ≤ degSensitivityExponent`
from Kushilevitz's 6-bit function and iterated composition. -/
theorem kushilevitz_exponent_lower_bound_proof :
    Real.log 6 / Real.log 3 ≤ degSensitivityExponent := by
  simpa using degSensitivityExponent_ge_log_div_log (n := 6) (d := 3) (by decide) (by decide)
    kushilevitzFun kushilevitzFun_deg_le kushilevitzFun_normalized.1 kushilevitzFun_normalized.2

/-- Composed witness `(n = 9, deg = 4, s = 9)` given by `NAE₃ ∘ NAE₃`. -/
theorem nae3_comp_nae3_witness_proof :
    ∃ f : BooleanFun 9, polyDegree f = 4 ∧ maxSensitivity f = 9 := by
  let f : BooleanFun 9 := composeBool nae3Fun nae3Fun
  have h0 : f (zeroVec 9) = false := composeBool_zero nae3Fun_normalized.1 nae3Fun_normalized.1
  have h1 : ∀ i : Fin 9, f (basisVec i) = true :=
    composeBool_basis nae3Fun_normalized.1 nae3Fun_normalized.2 nae3Fun_normalized.2
  have hsens : maxSensitivity f = 9 := maxSensitivity_eq_dim_of_normalized h0 h1
  have hle : polyDegree f ≤ 4 := by
    calc polyDegree f ≤ polyDegree nae3Fun * polyDegree nae3Fun := polyDegree_composeBool_le _ _
      _ ≤ 2 * 2 := Nat.mul_le_mul nae3Fun_deg_le nae3Fun_deg_le
  have hgt3 : ¬ polyDegree f ≤ 3 := by
    intro h3
    have := maxSensitivity_le_six_of_deg_le_three_proof 9 f h3
    omega
  exact ⟨f, by omega, hsens⟩

/-- 9-bit outer Boolean function `outerG9` of weighted degree `≤ 5` under
weights `(2, 2, 1, 1, 1, 1, 1, 1, 1)`. -/
def outerG9Tree : BoolTree 9 :=
  (.node
    (.node
      (.node
        (.node
          (.node
            (bt4 (bt2 false true true true) (bt2 true true true true) (bt2 true true true true) (bt2 true true true true))
            (bt4 (bt2 true true true true) (bt2 true false true false) (bt2 true true true true) (bt2 false false false false)))
          (.node
            (bt4 (bt2 true true true true) (bt2 true false false false) (bt2 true false true false) (bt2 false false false false))
            (bt4 (bt2 true false true true) (bt2 true false false false) (bt2 false false false false) (bt2 false false false false))))
        (.node
          (.node
            (bt4 (bt2 true true true true) (bt2 true true true true) (bt2 true false true false) (bt2 false false true false))
            (bt4 (bt2 true true true true) (bt2 true false true false) (bt2 true false true false) (bt2 false false false false)))
          (.node
            (bt4 (bt2 true true true true) (bt2 true false false false) (bt2 true false true false) (bt2 false false false false))
            (bt4 (bt2 false false false false) (bt2 true false false false) (bt2 false false false false) (bt2 false false false true)))))
      (.node
        (.node
          (.node
            (bt4 (bt2 true true true true) (bt2 true true false true) (bt2 true true true true) (bt2 true true true true))
            (bt4 (bt2 true true false true) (bt2 true true false true) (bt2 true true true true) (bt2 true true true true)))
          (.node
            (bt4 (bt2 true true true true) (bt2 true true false true) (bt2 true true true false) (bt2 false true false false))
            (bt4 (bt2 true false true true) (bt2 true true false true) (bt2 true true true false) (bt2 true true true false))))
        (.node
          (.node
            (bt4 (bt2 true false false false) (bt2 true false false false) (bt2 false false false false) (bt2 false false true false))
            (bt4 (bt2 true true false true) (bt2 true false false false) (bt2 false false false false) (bt2 false false false false)))
          (.node
            (bt4 (bt2 false false false false) (bt2 true false false false) (bt2 false true false false) (bt2 false true false false))
            (bt4 (bt2 false false false false) (bt2 true false false false) (bt2 false true false false) (bt2 false false false false))))))
    (.node
      (.node
        (.node
          (.node
            (bt4 (bt2 true true true false) (bt2 true true true true) (bt2 true true false true) (bt2 true true false true))
            (bt4 (bt2 true true true false) (bt2 true true true false) (bt2 true true true true) (bt2 true true false false)))
          (.node
            (bt4 (bt2 true true false false) (bt2 true false false false) (bt2 true true false true) (bt2 true true false true))
            (bt4 (bt2 true true true true) (bt2 true true false false) (bt2 false true false true) (bt2 true true false false))))
        (.node
          (.node
            (bt4 (bt2 true true false false) (bt2 false true false true) (bt2 true false false false) (bt2 false false false false))
            (bt4 (bt2 false true false false) (bt2 false true false false) (bt2 true false true false) (bt2 true true false false)))
          (.node
            (bt4 (bt2 true true false false) (bt2 true false false false) (bt2 true false false false) (bt2 true false false false))
            (bt4 (bt2 false true false false) (bt2 true true false false) (bt2 false false false false) (bt2 true false false false)))))
      (.node
        (.node
          (.node
            (bt4 (bt2 true false true false) (bt2 false false false true) (bt2 false false false true) (bt2 false false false true))
            (bt4 (bt2 false false false false) (bt2 false true false true) (bt2 false false true true) (bt2 true true true true)))
          (.node
            (bt4 (bt2 false false false false) (bt2 false false false true) (bt2 false true false true) (bt2 false true false true))
            (bt4 (bt2 false false true true) (bt2 false true false true) (bt2 false true true true) (bt2 true true true false))))
        (.node
          (.node
            (bt4 (bt2 true false false false) (bt2 false false false true) (bt2 false false false true) (bt2 false false true true))
            (bt4 (bt2 false true false true) (bt2 false true false true) (bt2 false false true true) (bt2 true true true true)))
          (.node
            (bt4 (bt2 false false false false) (bt2 true false true true) (bt2 false true false true) (bt2 true true true true))
            (bt4 (bt2 false true true true) (bt2 true true true true) (bt2 false true true true) (bt2 true false true false)))))))

/-- Weight profile `(2, 2, 1, 1, 1, 1, 1, 1, 1)` for `outerG9Tree`. -/
def weights13 : Fin 9 → ℕ := ![2, 2, 1, 1, 1, 1, 1, 1, 1]


def ct2 (a b c d : ℤ) : CubeTree 2 :=
  .node (.node (.leaf a) (.leaf b)) (.node (.leaf c) (.leaf d))

def ct4 (a b c d : CubeTree 2) : CubeTree 4 :=
  .node (.node a b) (.node c d)

private def og_t0 : CubeTree 8 := (.node
    (.node
      (.node
        (.node
          (ct4 (ct2 0 1 1 1) (ct2 1 1 1 1) (ct2 1 1 1 1) (ct2 1 1 1 1))
          (ct4 (ct2 1 1 1 1) (ct2 1 0 1 0) (ct2 1 1 1 1) (ct2 0 0 0 0)))
        (.node
          (ct4 (ct2 1 1 1 1) (ct2 1 0 0 0) (ct2 1 0 1 0) (ct2 0 0 0 0))
          (ct4 (ct2 1 0 1 1) (ct2 1 0 0 0) (ct2 0 0 0 0) (ct2 0 0 0 0))))
      (.node
        (.node
          (ct4 (ct2 1 1 1 1) (ct2 1 1 1 1) (ct2 1 0 1 0) (ct2 0 0 1 0))
          (ct4 (ct2 1 1 1 1) (ct2 1 0 1 0) (ct2 1 0 1 0) (ct2 0 0 0 0)))
        (.node
          (ct4 (ct2 1 1 1 1) (ct2 1 0 0 0) (ct2 1 0 1 0) (ct2 0 0 0 0))
          (ct4 (ct2 0 0 0 0) (ct2 1 0 0 0) (ct2 0 0 0 0) (ct2 0 0 0 1)))))
    (.node
      (.node
        (.node
          (ct4 (ct2 1 1 1 1) (ct2 1 1 0 1) (ct2 1 1 1 1) (ct2 1 1 1 1))
          (ct4 (ct2 1 1 0 1) (ct2 1 1 0 1) (ct2 1 1 1 1) (ct2 1 1 1 1)))
        (.node
          (ct4 (ct2 1 1 1 1) (ct2 1 1 0 1) (ct2 1 1 1 0) (ct2 0 1 0 0))
          (ct4 (ct2 1 0 1 1) (ct2 1 1 0 1) (ct2 1 1 1 0) (ct2 1 1 1 0))))
      (.node
        (.node
          (ct4 (ct2 1 0 0 0) (ct2 1 0 0 0) (ct2 0 0 0 0) (ct2 0 0 1 0))
          (ct4 (ct2 1 1 0 1) (ct2 1 0 0 0) (ct2 0 0 0 0) (ct2 0 0 0 0)))
        (.node
          (ct4 (ct2 0 0 0 0) (ct2 1 0 0 0) (ct2 0 1 0 0) (ct2 0 1 0 0))
          (ct4 (ct2 0 0 0 0) (ct2 1 0 0 0) (ct2 0 1 0 0) (ct2 0 0 0 0))))))
private def og_t1 : CubeTree 8 := (.node
    (.node
      (.node
        (.node
          (ct4 (ct2 1 0 0 (-1)) (ct2 0 0 0 0) (ct2 0 0 (-1) 0) (ct2 0 0 (-1) 0))
          (ct4 (ct2 0 0 0 (-1)) (ct2 0 1 0 0) (ct2 0 0 0 0) (ct2 1 1 0 0)))
        (.node
          (ct4 (ct2 0 0 (-1) (-1)) (ct2 0 0 0 0) (ct2 0 1 (-1) 1) (ct2 1 1 0 1))
          (ct4 (ct2 0 1 0 0) (ct2 0 1 0 0) (ct2 0 1 0 1) (ct2 1 1 0 0))))
      (.node
        (.node
          (ct4 (ct2 0 0 (-1) (-1)) (ct2 (-1) 0 (-1) 0) (ct2 0 0 (-1) 0) (ct2 0 0 (-1) 0))
          (ct4 (ct2 (-1) 0 (-1) (-1)) (ct2 (-1) 1 (-1) 0) (ct2 0 0 0 0) (ct2 1 1 0 0)))
        (.node
          (ct4 (ct2 0 0 (-1) (-1)) (ct2 0 0 0 0) (ct2 0 0 (-1) 0) (ct2 1 0 0 0))
          (ct4 (ct2 0 1 0 0) (ct2 0 1 0 0) (ct2 0 0 0 0) (ct2 1 0 0 (-1))))))
    (.node
      (.node
        (.node
          (ct4 (ct2 0 (-1) 0 (-1)) (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) (-1) 0) (ct2 (-1) (-1) (-1) 0))
          (ct4 (ct2 (-1) (-1) 0 (-1)) (ct2 (-1) 0 0 0) (ct2 (-1) (-1) 0 0) (ct2 0 0 0 0)))
        (.node
          (ct4 (ct2 (-1) (-1) (-1) (-1)) (ct2 (-1) (-1) 0 0) (ct2 (-1) 0 (-1) 1) (ct2 0 0 0 1))
          (ct4 (ct2 (-1) 0 0 0) (ct2 (-1) 0 0 0) (ct2 (-1) 0 0 1) (ct2 0 0 0 0))))
      (.node
        (.node
          (ct4 (ct2 0 0 0 0) (ct2 (-1) 0 0 1) (ct2 0 0 0 1) (ct2 0 0 0 1))
          (ct4 (ct2 (-1) 0 0 0) (ct2 (-1) 1 0 1) (ct2 0 0 1 1) (ct2 1 1 1 1)))
        (.node
          (ct4 (ct2 0 0 0 0) (ct2 0 0 1 1) (ct2 0 0 0 1) (ct2 1 0 1 1))
          (ct4 (ct2 0 1 1 1) (ct2 0 1 1 1) (ct2 0 0 1 1) (ct2 1 0 1 0))))))
private def og_t00 : CubeTree 7 := (.node
    (.node
      (.node
        (ct4 (ct2 0 1 1 1) (ct2 1 1 1 1) (ct2 1 1 1 1) (ct2 1 1 1 1))
        (ct4 (ct2 1 1 1 1) (ct2 1 0 1 0) (ct2 1 1 1 1) (ct2 0 0 0 0)))
      (.node
        (ct4 (ct2 1 1 1 1) (ct2 1 0 0 0) (ct2 1 0 1 0) (ct2 0 0 0 0))
        (ct4 (ct2 1 0 1 1) (ct2 1 0 0 0) (ct2 0 0 0 0) (ct2 0 0 0 0))))
    (.node
      (.node
        (ct4 (ct2 1 1 1 1) (ct2 1 1 1 1) (ct2 1 0 1 0) (ct2 0 0 1 0))
        (ct4 (ct2 1 1 1 1) (ct2 1 0 1 0) (ct2 1 0 1 0) (ct2 0 0 0 0)))
      (.node
        (ct4 (ct2 1 1 1 1) (ct2 1 0 0 0) (ct2 1 0 1 0) (ct2 0 0 0 0))
        (ct4 (ct2 0 0 0 0) (ct2 1 0 0 0) (ct2 0 0 0 0) (ct2 0 0 0 1)))))
private def og_t01 : CubeTree 7 := (.node
    (.node
      (.node
        (ct4 (ct2 1 0 0 0) (ct2 0 0 (-1) 0) (ct2 0 0 0 0) (ct2 0 0 0 0))
        (ct4 (ct2 0 0 (-1) 0) (ct2 0 1 (-1) 1) (ct2 0 0 0 0) (ct2 1 1 1 1)))
      (.node
        (ct4 (ct2 0 0 0 0) (ct2 0 1 0 1) (ct2 0 1 0 0) (ct2 0 1 0 0))
        (ct4 (ct2 0 0 0 0) (ct2 0 1 0 1) (ct2 1 1 1 0) (ct2 1 1 1 0))))
    (.node
      (.node
        (ct4 (ct2 0 (-1) (-1) (-1)) (ct2 0 (-1) (-1) (-1)) (ct2 (-1) 0 (-1) 0) (ct2 0 0 0 0))
        (ct4 (ct2 0 0 (-1) 0) (ct2 0 0 (-1) 0) (ct2 (-1) 0 (-1) 0) (ct2 0 0 0 0)))
      (.node
        (ct4 (ct2 (-1) (-1) (-1) (-1)) (ct2 0 0 0 0) (ct2 (-1) 1 (-1) 0) (ct2 0 1 0 0))
        (ct4 (ct2 0 0 0 0) (ct2 0 0 0 0) (ct2 0 1 0 0) (ct2 0 0 0 (-1))))))
private def og_t10 : CubeTree 7 := (.node
    (.node
      (.node
        (ct4 (ct2 1 0 0 (-1)) (ct2 0 0 0 0) (ct2 0 0 (-1) 0) (ct2 0 0 (-1) 0))
        (ct4 (ct2 0 0 0 (-1)) (ct2 0 1 0 0) (ct2 0 0 0 0) (ct2 1 1 0 0)))
      (.node
        (ct4 (ct2 0 0 (-1) (-1)) (ct2 0 0 0 0) (ct2 0 1 (-1) 1) (ct2 1 1 0 1))
        (ct4 (ct2 0 1 0 0) (ct2 0 1 0 0) (ct2 0 1 0 1) (ct2 1 1 0 0))))
    (.node
      (.node
        (ct4 (ct2 0 0 (-1) (-1)) (ct2 (-1) 0 (-1) 0) (ct2 0 0 (-1) 0) (ct2 0 0 (-1) 0))
        (ct4 (ct2 (-1) 0 (-1) (-1)) (ct2 (-1) 1 (-1) 0) (ct2 0 0 0 0) (ct2 1 1 0 0)))
      (.node
        (ct4 (ct2 0 0 (-1) (-1)) (ct2 0 0 0 0) (ct2 0 0 (-1) 0) (ct2 1 0 0 0))
        (ct4 (ct2 0 1 0 0) (ct2 0 1 0 0) (ct2 0 0 0 0) (ct2 1 0 0 (-1))))))
private def og_t11 : CubeTree 7 := (.node
    (.node
      (.node
        (ct4 (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0))
        (ct4 (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0)))
      (.node
        (ct4 (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0))
        (ct4 (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0))))
    (.node
      (.node
        (ct4 (ct2 0 0 1 1) (ct2 0 0 1 1) (ct2 0 0 1 1) (ct2 0 0 1 1))
        (ct4 (ct2 0 0 1 1) (ct2 0 0 1 1) (ct2 0 0 1 1) (ct2 0 0 1 1)))
      (.node
        (ct4 (ct2 0 0 1 1) (ct2 0 0 1 1) (ct2 0 0 1 1) (ct2 0 0 1 1))
        (ct4 (ct2 0 0 1 1) (ct2 0 0 1 1) (ct2 0 0 1 1) (ct2 0 0 1 1)))))
private def og_t000 : CubeTree 6 := (.node
    (.node
      (ct4 (ct2 0 1 1 1) (ct2 1 1 1 1) (ct2 1 1 1 1) (ct2 1 1 1 1))
      (ct4 (ct2 1 1 1 1) (ct2 1 0 1 0) (ct2 1 1 1 1) (ct2 0 0 0 0)))
    (.node
      (ct4 (ct2 1 1 1 1) (ct2 1 0 0 0) (ct2 1 0 1 0) (ct2 0 0 0 0))
      (ct4 (ct2 1 0 1 1) (ct2 1 0 0 0) (ct2 0 0 0 0) (ct2 0 0 0 0))))
private def og_t001 : CubeTree 6 := (.node
    (.node
      (ct4 (ct2 1 0 0 0) (ct2 0 0 0 0) (ct2 0 (-1) 0 (-1)) (ct2 (-1) (-1) 0 (-1)))
      (ct4 (ct2 0 0 0 0) (ct2 0 0 0 0) (ct2 0 (-1) 0 (-1)) (ct2 0 0 0 0)))
    (.node
      (ct4 (ct2 0 0 0 0) (ct2 0 0 0 0) (ct2 0 0 0 0) (ct2 0 0 0 0))
      (ct4 (ct2 (-1) 0 (-1) (-1)) (ct2 0 0 0 0) (ct2 0 0 0 0) (ct2 0 0 0 1))))
private def og_t010 : CubeTree 6 := (.node
    (.node
      (ct4 (ct2 1 0 0 0) (ct2 0 0 (-1) 0) (ct2 0 0 0 0) (ct2 0 0 0 0))
      (ct4 (ct2 0 0 (-1) 0) (ct2 0 1 (-1) 1) (ct2 0 0 0 0) (ct2 1 1 1 1)))
    (.node
      (ct4 (ct2 0 0 0 0) (ct2 0 1 0 1) (ct2 0 1 0 0) (ct2 0 1 0 0))
      (ct4 (ct2 0 0 0 0) (ct2 0 1 0 1) (ct2 1 1 1 0) (ct2 1 1 1 0))))
private def og_t011 : CubeTree 6 := (.node
    (.node
      (ct4 (ct2 (-1) (-1) (-1) (-1)) (ct2 0 (-1) 0 (-1)) (ct2 (-1) 0 (-1) 0) (ct2 0 0 0 0))
      (ct4 (ct2 0 0 0 0) (ct2 0 (-1) 0 (-1)) (ct2 (-1) 0 (-1) 0) (ct2 (-1) (-1) (-1) (-1))))
    (.node
      (ct4 (ct2 (-1) (-1) (-1) (-1)) (ct2 0 (-1) 0 (-1)) (ct2 (-1) 0 (-1) 0) (ct2 0 0 0 0))
      (ct4 (ct2 0 0 0 0) (ct2 0 (-1) 0 (-1)) (ct2 (-1) 0 (-1) 0) (ct2 (-1) (-1) (-1) (-1)))))
private def og_t100 : CubeTree 6 := (.node
    (.node
      (ct4 (ct2 1 0 0 (-1)) (ct2 0 0 0 0) (ct2 0 0 (-1) 0) (ct2 0 0 (-1) 0))
      (ct4 (ct2 0 0 0 (-1)) (ct2 0 1 0 0) (ct2 0 0 0 0) (ct2 1 1 0 0)))
    (.node
      (ct4 (ct2 0 0 (-1) (-1)) (ct2 0 0 0 0) (ct2 0 1 (-1) 1) (ct2 1 1 0 1))
      (ct4 (ct2 0 1 0 0) (ct2 0 1 0 0) (ct2 0 1 0 1) (ct2 1 1 0 0))))
private def og_t101 : CubeTree 6 := (.node
    (.node
      (ct4 (ct2 (-1) 0 (-1) 0) (ct2 (-1) 0 (-1) 0) (ct2 0 0 0 0) (ct2 0 0 0 0))
      (ct4 (ct2 (-1) 0 (-1) 0) (ct2 (-1) 0 (-1) 0) (ct2 0 0 0 0) (ct2 0 0 0 0)))
    (.node
      (ct4 (ct2 0 0 0 0) (ct2 0 0 0 0) (ct2 0 (-1) 0 (-1)) (ct2 0 (-1) 0 (-1)))
      (ct4 (ct2 0 0 0 0) (ct2 0 0 0 0) (ct2 0 (-1) 0 (-1)) (ct2 0 (-1) 0 (-1)))))
private def og_t110 : CubeTree 6 := (.node
    (.node
      (ct4 (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0))
      (ct4 (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0)))
    (.node
      (ct4 (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0))
      (ct4 (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0) (ct2 (-1) (-1) 0 0))))
private def og_t111 : CubeTree 6 := (.node
    (.node
      (ct4 (ct2 1 1 1 1) (ct2 1 1 1 1) (ct2 1 1 1 1) (ct2 1 1 1 1))
      (ct4 (ct2 1 1 1 1) (ct2 1 1 1 1) (ct2 1 1 1 1) (ct2 1 1 1 1)))
    (.node
      (ct4 (ct2 1 1 1 1) (ct2 1 1 1 1) (ct2 1 1 1 1) (ct2 1 1 1 1))
      (ct4 (ct2 1 1 1 1) (ct2 1 1 1 1) (ct2 1 1 1 1) (ct2 1 1 1 1))))

private lemma outerG9_wdeg_check :
    outerG9Tree.toCubeTree.mobius.checkWeightedDegList [2, 2, 1, 1, 1, 1, 1, 1, 1] 0 5 = true := by
  have h000 : og_t000.mobius.checkWeightedDegList [1, 1, 1, 1, 1, 1] 0 5 = true := by decide
  have h001 : og_t001.mobius.checkWeightedDegList [1, 1, 1, 1, 1, 1] 1 5 = true := by decide
  have h010 : og_t010.mobius.checkWeightedDegList [1, 1, 1, 1, 1, 1] 2 5 = true := by decide
  have h011 : og_t011.mobius.checkWeightedDegList [1, 1, 1, 1, 1, 1] 3 5 = true := by decide
  have h100 : og_t100.mobius.checkWeightedDegList [1, 1, 1, 1, 1, 1] 2 5 = true := by decide
  have h101 : og_t101.mobius.checkWeightedDegList [1, 1, 1, 1, 1, 1] 3 5 = true := by decide
  have h110 : og_t110.mobius.checkWeightedDegList [1, 1, 1, 1, 1, 1] 4 5 = true := by decide
  have h111 : og_t111.mobius.checkWeightedDegList [1, 1, 1, 1, 1, 1] 5 5 = true := by decide
  have h00 : og_t00.mobius.checkWeightedDegList [1, 1, 1, 1, 1, 1, 1] 0 5 = true :=
    CubeTree.checkWeightedDegList_node_mobius og_t000 _ og_t001 1 _ 0 5 rfl h000 h001
  have h01 : og_t01.mobius.checkWeightedDegList [1, 1, 1, 1, 1, 1, 1] 2 5 = true :=
    CubeTree.checkWeightedDegList_node_mobius og_t010 _ og_t011 1 _ 2 5 rfl h010 h011
  have h10 : og_t10.mobius.checkWeightedDegList [1, 1, 1, 1, 1, 1, 1] 2 5 = true :=
    CubeTree.checkWeightedDegList_node_mobius og_t100 _ og_t101 1 _ 2 5 rfl h100 h101
  have h11 : og_t11.mobius.checkWeightedDegList [1, 1, 1, 1, 1, 1, 1] 4 5 = true :=
    CubeTree.checkWeightedDegList_node_mobius og_t110 _ og_t111 1 _ 4 5 rfl h110 h111
  have h0 : og_t0.mobius.checkWeightedDegList [2, 1, 1, 1, 1, 1, 1, 1] 0 5 = true :=
    CubeTree.checkWeightedDegList_node_mobius og_t00 _ og_t01 2 _ 0 5 rfl h00 h01
  have h1 : og_t1.mobius.checkWeightedDegList [2, 1, 1, 1, 1, 1, 1, 1] 2 5 = true :=
    CubeTree.checkWeightedDegList_node_mobius og_t10 _ og_t11 2 _ 2 5 rfl h10 h11
  exact CubeTree.checkWeightedDegList_node_mobius og_t0 _ og_t1 2 _ 0 5 rfl h0 h1

lemma outerG9_weighted_deg :
    ∀ S : Finset (Fin 9), 5 < ∑ i ∈ S, weights13 i → mobiusCoeff outerG9Tree.eval S = 0 :=
  mobiusCoeff_eq_zero_of_checkWeightedDeg outerG9Tree [2, 2, 1, 1, 1, 1, 1, 1, 1] weights13
    (by decide) 5 outerG9_wdeg_check

lemma outerG9_normalized :
    outerG9Tree.eval (zeroVec 9) = false ∧ ∀ i : Fin 9, outerG9Tree.eval (basisVec i) = true :=
  outerG9Tree.normalized_of_check (by decide)

/-- The 9 inner functions on `Fin 13`: two disjoint `NAE₃` blocks on `(0, 1, 2)` and `(3, 4, 5)`,
plus the 7 coordinate projections `(6, Ellipsis, 12)`. -/
def inner13 : Fin 9 → BooleanFun 13
  | ⟨0, _⟩ => fun x => nae3Fun ![x 0, x 1, x 2]
  | ⟨1, _⟩ => fun x => nae3Fun ![x 3, x 4, x 5]
  | ⟨2, _⟩ => fun x => x 6
  | ⟨3, _⟩ => fun x => x 7
  | ⟨4, _⟩ => fun x => x 8
  | ⟨5, _⟩ => fun x => x 9
  | ⟨6, _⟩ => fun x => x 10
  | ⟨7, _⟩ => fun x => x 11
  | ⟨8, _⟩ => fun x => x 12

private lemma polyDegree_coord_le_one (j : Fin 13) :
    polyDegree (fun x : Fin 13 → Bool => x j) ≤ 1 := by
  rw [polyDegree_le_iff]
  refine ⟨MvPolynomial.X j, ?_, by simp [MvPolynomial.totalDegree_X]⟩
  intro x
  simp

private lemma polyDegree_nae3_block_le_two (a b c : Fin 13) :
    polyDegree (fun x : Fin 13 → Bool => nae3Fun ![x a, x b, x c]) ≤ 2 := by
  rw [polyDegree_le_iff]
  obtain ⟨P, hPrep, hPdeg⟩ := polyDegree_le_iff.mp nae3Fun_deg_le
  let φ : Fin 3 → MvPolynomial (Fin 13) ℝ := ![MvPolynomial.X a, MvPolynomial.X b, MvPolynomial.X c]
  refine ⟨MvPolynomial.aeval φ P, ?_, ?_⟩
  · intro x
    change MvPolynomial.eval (fun j => boolToReal (x j)) (MvPolynomial.aeval φ P) =
      boolToReal (nae3Fun ![x a, x b, x c])
    rw [eval_aeval_eq]
    have harg : (fun i : Fin 3 => MvPolynomial.eval (fun j => boolToReal (x j)) (φ i)) =
        (fun i : Fin 3 => boolToReal ((![x a, x b, x c] : Fin 3 → Bool) i)) := by
      funext i; fin_cases i <;> simp [φ]
    rw [harg]
    exact hPrep ![x a, x b, x c]
  · refine (totalDegree_aeval_le φ P ?_).trans hPdeg
    intro i; fin_cases i <;> simp [φ, MvPolynomial.totalDegree_X]

private lemma inner13_deg_le (i : Fin 9) : polyDegree (inner13 i) ≤ weights13 i := by
  fin_cases i
  · exact polyDegree_nae3_block_le_two 0 1 2
  · exact polyDegree_nae3_block_le_two 3 4 5
  · exact polyDegree_coord_le_one 6
  · exact polyDegree_coord_le_one 7
  · exact polyDegree_coord_le_one 8
  · exact polyDegree_coord_le_one 9
  · exact polyDegree_coord_le_one 10
  · exact polyDegree_coord_le_one 11
  · exact polyDegree_coord_le_one 12

/-- Explicit `(n = 13, deg = 5, s = 13)` Boolean function `outerG9(NAE₃, NAE₃, x₆..x₁₂)`. -/
def deg5Sens13Fun : BooleanFun 13 :=
  fun x => outerG9Tree.eval (fun i => inner13 i x)

/-- Explicit witness `(n = 13, deg = 5, s = 13)` proving `B_5 ≥ 13`. -/
theorem deg5_sens13_witness_proof :
    ∃ f : BooleanFun 13, polyDegree f = 5 ∧ maxSensitivity f = 13 := by
  refine ⟨deg5Sens13Fun, ?_, ?_⟩
  · have hle : polyDegree deg5Sens13Fun ≤ 5 :=
      polyDegree_weightedCompose_le outerG9Tree.eval weights13 inner13
        outerG9_weighted_deg inner13_deg_le
    have h0 : deg5Sens13Fun (zeroVec 13) = false := by decide
    have h1 : ∀ i : Fin 13, deg5Sens13Fun (basisVec i) = true := by decide
    have hsens : maxSensitivity deg5Sens13Fun = 13 := maxSensitivity_eq_dim_of_normalized h0 h1
    have hgt4 : ¬ polyDegree deg5Sens13Fun ≤ 4 := by
      intro h4
      have := maxSensitivity_le_nine_of_deg_le_four_proof 13 deg5Sens13Fun h4
      omega
    omega
  · have h0 : deg5Sens13Fun (zeroVec 13) = false := by decide
    have h1 : ∀ i : Fin 13, deg5Sens13Fun (basisVec i) = true := by decide
    exact maxSensitivity_eq_dim_of_normalized h0 h1

end DegreeSensitivity
