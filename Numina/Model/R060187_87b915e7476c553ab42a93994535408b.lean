import Mathlib

theorem algebra_14309 (x : ℝ) (h : (2 : ℝ) ^ (3 * x) = 7) : (8 : ℝ) ^ (x + 1) = 56 := by
  have h1 : (8 : ℝ) ^ (x + 1) = (2 : ℝ) ^ (3 * (x + 1)) := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    ring_nf
    all_goals norm_num
  have h2 : (2 : ℝ) ^ (3 * (x + 1)) = (2 : ℝ) ^ (3 * x + 3 : ℝ) := by
    ring_nf
  have h3 : (2 : ℝ) ^ (3 * x + 3 : ℝ) = (2 : ℝ) ^ (3 * x : ℝ) * (2 : ℝ) ^ (3 : ℝ) := by
    rw [← Real.rpow_add]
    ring_nf
    all_goals norm_num
  rw [h1, h2, h3, h]
  all_goals norm_num