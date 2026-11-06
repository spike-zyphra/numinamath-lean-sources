import Mathlib

theorem algebra_211615 (math_test correction_test other_math_grades : ℝ)
    (h₀ : 0 < math_test ∧ 0 < correction_test)
    (h₁ : other_math_grades > (math_test + correction_test) / 2) :
    (math_test + correction_test + other_math_grades) / 3 > (math_test + correction_test) / 2 := by 
  linarith