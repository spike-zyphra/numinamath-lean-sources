import Mathlib

theorem algebra_105078 (x : ℝ) (hx : x = 16 / (2 * 12 + 8)) :
    x * 12 = 6 := by
  rw [hx]
  norm_num