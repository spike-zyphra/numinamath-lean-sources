import Mathlib

theorem algebra_10973 : Real.sqrt ((16/25) + (9/4)) = 17/10 := by
  have h1 : (16 / 25 : ℝ) + (9 / 4 : ℝ) = (289 / 100 : ℝ) := by norm_num
  rw [h1]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num