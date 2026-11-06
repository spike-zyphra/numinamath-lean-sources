import Mathlib

theorem algebra_172372 {x : ℝ} (hx : x = (2^3)^4) :
    x ^ ((1 : ℝ) / 3) = 2^4 := by
  rw [hx]
  have h1 : ((2 ^ 3 : ℝ) ^ 4) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ (4 : ℝ) := by
    rw [show ((2 ^ 3 : ℝ) ^ 4) = (2 : ℝ) ^ (12 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  rw [h1]
  all_goals norm_num