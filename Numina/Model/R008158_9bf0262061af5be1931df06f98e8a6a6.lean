import Mathlib

theorem algebra_11069 (total_apples : ℝ) (h : total_apples = 5.5) :
    (total_apples * (1 - 20 / 100)) * 50 / 100 = 2.2 := by
  rw [h]
  norm_num