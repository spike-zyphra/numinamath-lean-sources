import Mathlib

theorem algebra_264214 : (Real.sqrt (25 - 16)) / (Real.sqrt 25 - Real.sqrt 16) = 3 := by
  have h1 : Real.sqrt (25 - 16 : ℝ) = 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h2 : Real.sqrt (25 : ℝ) = 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h3 : Real.sqrt (16 : ℝ) = 4 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h1, h2, h3]
  all_goals norm_num