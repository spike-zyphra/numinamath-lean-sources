import Mathlib

theorem algebra_10310 : Real.sqrt (0.000064 ^ ((1 : ℝ) / 3)) = 0.2 := by
  have h1 : (0.000064 : ℝ) ^ ((1 : ℝ) / 3) = 0.04 := by 
    rw [show (0.000064 : ℝ) = (0.04 : ℝ) ^ (3 : ℝ) by norm_num]
    have h2 : ((0.04 : ℝ) ^ (3 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) = (0.04 : ℝ) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num -- check the base is non-negative
    rw [h2]
  rw [h1]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  all_goals norm_num