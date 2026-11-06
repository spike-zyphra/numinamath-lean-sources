import Mathlib

theorem algebra_121886 (x : ℝ) (hx : x = 5 * 0.06) :
    (x - 1 * 0.06 + 2 * 0.0) / (5 - 1 + 2) = 0.04 := by
  rw [hx]
  norm_num