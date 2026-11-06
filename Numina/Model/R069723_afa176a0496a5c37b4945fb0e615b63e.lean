import Mathlib

theorem algebra_7089 (x : ℝ) (hx : x = 3.652264) :
    (x : ℝ) ^ ((1 : ℝ) / 3) = 1.54 := by
  rw [hx]
  have h2 : (3.652264 : ℝ) = (1.54 : ℝ) ^ (3 : ℝ) := by norm_num
  rw [h2]
  have h3 : ((1.54 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = (1.54 : ℝ) := by
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  exact h3