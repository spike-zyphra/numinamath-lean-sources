import Mathlib

theorem algebra_93246 : Real.sqrt (16 * Real.sqrt (8 * Real.sqrt 4)) = 8 := by
  have h1 : Real.sqrt (4 : ℝ) = 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h2 : Real.sqrt (8 * Real.sqrt 4 : ℝ) = 4 := by
    rw [h1]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h2]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num