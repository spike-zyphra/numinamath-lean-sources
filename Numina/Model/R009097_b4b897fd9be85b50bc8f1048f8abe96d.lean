import Mathlib

theorem algebra_96904 : (625 : ℝ) ^ ((Real.logb 5 2015) / 4) = 2015 := by
  have h1 : (625 : ℝ) = 5 ^ (4 : ℝ) := by norm_num
  rw [h1]
  have h2 : ((5 : ℝ) ^ (4 : ℝ)) ^ ((Real.logb 5 2015) / 4) = (5 : ℝ) ^ (Real.logb 5 2015 : ℝ) := by
    rw [← Real.rpow_mul]
    ring_nf -- need to simplify ((4 * (Real.logb 5 2015) / 4 )) to (Real.logb 5 2015)
    all_goals norm_num -- deals with the base being positive
  rw [h2]
  have h3 : (5 : ℝ) ^ (Real.logb 5 2015 : ℝ) = 2015 := by
    rw [Real.rpow_logb]
    all_goals norm_num -- confirms that the base and the logarithm base match, and the value is positive
  rw [h3]