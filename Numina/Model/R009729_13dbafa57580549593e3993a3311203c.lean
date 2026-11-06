import Mathlib

theorem algebra_10670 {x : ℝ} (hx : (5 : ℝ) ^ x = 100) : (5 : ℝ) ^ (x + 2) = 2500 := by
  have h1 : (5 : ℝ) ^ (x + 2) = (5 : ℝ) ^ x * (5 : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_add]
    all_goals norm_num
  rw [h1, hx]
  norm_num