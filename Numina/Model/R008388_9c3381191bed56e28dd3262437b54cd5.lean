import Mathlib

theorem algebra_13913 (total_parts : ℕ) (h : total_parts = 7 + 1) :
    (7 / total_parts : ℚ) * 4 = 7 / 2 := by
  rw [h]
  norm_num