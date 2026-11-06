import Mathlib

theorem algebra_95131 (x : ℝ) (hx : 0 < x) (h : Real.logb 6 x = 2.5) :
    x = 36 * Real.sqrt 6 := by
  have h1 : x = (6 : ℝ) ^ (2.5 : ℝ) := by
    rw [Real.logb_eq_iff_rpow_eq] at h
    all_goals linarith
    all_goals linarith
  have h2 : (6 : ℝ) ^ (2.5 : ℝ) = (6 : ℝ) ^ (2 : ℝ) * (6 : ℝ) ^ (0.5 : ℝ) := by
    rw [show (2.5 : ℝ) = (2 : ℝ) + (0.5 : ℝ) by norm_num]
    rw [Real.rpow_add]
    all_goals norm_num
  have h3 : (6 : ℝ) ^ (2 : ℝ) = (36 : ℝ) := by
    norm_num
  have h4 : (6 : ℝ) ^ (0.5 : ℝ) = Real.sqrt 6 := by
    rw [Real.sqrt_eq_rpow]
    all_goals norm_num
  rw [h1]
  rw [h2, h3, h4]
  all_goals norm_num
  <;> rw [Real.sqrt_nonneg]
  all_goals norm_num
  all_goals linarith