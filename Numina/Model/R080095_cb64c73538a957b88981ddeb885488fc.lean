import Mathlib

theorem algebra_234366 (total_sum : ℝ) (h : total_sum = 8 * 12) (removed_sum : ℝ)
    (h' : removed_sum = 2 * 18) :
    (total_sum - removed_sum) / 6 = 10 := by
  rw [h, h']
  norm_num