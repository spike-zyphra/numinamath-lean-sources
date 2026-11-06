import Mathlib

theorem algebra_3600: Real.sqrt (Real.sqrt ((2015 * 2016) * (2016 * 2017) + 2016 ^ 2)) = 2016 := by
  have h1 : Real.sqrt ((2015 * 2016 : ℝ) * (2016 * 2017) + (2016 : ℝ) ^ 2) = (2016 : ℝ) ^ 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h1]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num