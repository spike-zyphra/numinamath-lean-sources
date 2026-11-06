import Mathlib

theorem algebra_21876 : Real.sqrt (2.5^2 - 0.7^2) / (2.7 - 2.5) = 12 := by
  have h1 : Real.sqrt (2.5^2 - 0.7^2) = (2.4 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h1]
  norm_num