import Mathlib

theorem algebra_268248 : Real.sqrt (16 * Real.sqrt 16) = 2^3 := by
  have h1 : Real.sqrt 16 = (4 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h1]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num