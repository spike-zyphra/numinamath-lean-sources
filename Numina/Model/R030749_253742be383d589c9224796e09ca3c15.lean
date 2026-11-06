import Mathlib

theorem algebra_8272 : Real.sqrt ((-3)^2) = 3 ∧ 0 ≤ 3 ∧ 3^2 = (-3)^2 := by
  have h1 : Real.sqrt ((-3 : ℝ) ^ 2) = 3 := by
    rw [Real.sqrt_sq_eq_abs]
    norm_num
  constructor
  · exact h1
  constructor
  · norm_num
  · norm_num