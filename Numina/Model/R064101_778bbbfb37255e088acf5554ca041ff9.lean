import Mathlib

theorem algebra_3757 : (Real.sqrt (Real.sqrt (2016 * 2018 * (2015 ^ 2 + 8065) + 1))) = 2017 := by
  have h1 : Real.sqrt (2016 * 2018 * (2015 ^ 2 + 8065) + 1) = (2017 : ℝ) ^ 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h2 : Real.sqrt ((2017 : ℝ) ^ 2) = (2017 : ℝ) := by
    rw [Real.sqrt_sq (by norm_num)]
  rw [h1, h2]
  all_goals norm_num