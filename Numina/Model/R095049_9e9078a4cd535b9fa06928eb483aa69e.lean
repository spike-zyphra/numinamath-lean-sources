import Mathlib

theorem algebra_281928 (total_flour : ℝ) (h : total_flour = 4 + 1 / 2) :
    total_flour / 2 = 2 + 1 / 4 := by
  rw [h]
  norm_num