import Mathlib

theorem number_theory_230539 : (2016^2 + 2016 * 2017 + 2017^2 + 2016^3 : ℝ) ^ ((1 : ℝ) / 3) = 2017 := by
  have h1 : (2016^2 + 2016 * 2017 + 2017^2 + 2016^3 : ℝ) = (2017 : ℝ) ^ 3 := by
    norm_num
  rw [h1]
  -- Now we need to compute the cubic root of 2017^3
  -- which should be 2017
  have h2 : ((2017 : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (2017 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals norm_num
  rw [h2]