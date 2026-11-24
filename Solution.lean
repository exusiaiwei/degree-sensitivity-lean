module

public import DegreeSensitivity

public section

/-!
# Proved Solution: Low-Degree Sensitivity Bounds & Asymptotic Degree–Sensitivity Exponent

Connects every advertised theorem in `Challenge.lean` to its completed,
sorry-free proof in `DegreeSensitivity`, using only the standard Lean axioms
(`propext`, `Quot.sound`, `Classical.choice`).
-/

namespace DegreeSensitivity

theorem nae3_witness :
    ∃ f : BooleanFun 3, polyDegree f = 2 ∧ maxSensitivity f = 3 :=
  nae3_witness_proof

theorem kushilevitz_witness :
    ∃ f : BooleanFun 6, polyDegree f = 3 ∧ maxSensitivity f = 6 :=
  kushilevitz_witness_proof

theorem nae3_comp_nae3_witness :
    ∃ f : BooleanFun 9, polyDegree f = 4 ∧ maxSensitivity f = 9 :=
  nae3_comp_nae3_witness_proof

theorem deg5_sens13_witness :
    ∃ f : BooleanFun 13, polyDegree f = 5 ∧ maxSensitivity f = 13 :=
  deg5_sens13_witness_proof

theorem kushilevitz_exponent_lower_bound :
    Real.log 6 / Real.log 3 ≤ degSensitivityExponent :=
  kushilevitz_exponent_lower_bound_proof

theorem maxSensitivity_le_three_of_deg_le_two :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 2 → maxSensitivity f ≤ 3 :=
  maxSensitivity_le_three_of_deg_le_two_proof

theorem maxSensitivity_le_six_of_deg_le_three :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 3 → maxSensitivity f ≤ 6 :=
  maxSensitivity_le_six_of_deg_le_three_proof

theorem maxSensitivity_le_nine_of_deg_le_four :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 4 → maxSensitivity f ≤ 9 :=
  maxSensitivity_le_nine_of_deg_le_four_proof

theorem maxSensitivity_le_fourteen_of_deg_le_five :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 5 → maxSensitivity f ≤ 14 :=
  fun _ f hf => maxSensitivity_le_fourteen_of_deg_le_five_proof f hf

theorem maxSensitivity_le_twenty_of_deg_le_six :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 6 → maxSensitivity f ≤ 20 :=
  fun _ f hf => maxSensitivity_le_twenty_of_deg_le_six_proof f hf

theorem maxSensitivity_le_twentyeight_of_deg_le_seven :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 7 → maxSensitivity f ≤ 28 :=
  fun _ f hf => maxSensitivity_le_twentyeight_of_deg_le_seven_proof f hf

theorem maxSensitivity_le_thirtysix_of_deg_le_eight :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 8 → maxSensitivity f ≤ 36 :=
  fun _ f hf => maxSensitivity_le_thirtysix_of_deg_le_eight_proof f hf

theorem maxSensitivity_le_fortysix_of_deg_le_nine :
    ∀ (n : ℕ) (f : BooleanFun n), polyDegree f ≤ 9 → maxSensitivity f ≤ 46 :=
  fun _ f hf => maxSensitivity_le_fortysix_of_deg_le_nine_proof f hf

end DegreeSensitivity
