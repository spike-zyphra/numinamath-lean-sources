import Mathlib

theorem algebra_21172 (total : ℝ) (h : total = 100) :
    (total - (65 + 18 + 10)) / total * 100 = 7 := by
  rw [h]
  norm_num