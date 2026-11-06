import Mathlib

theorem algebra_20789 (n : ℝ) (hn : n > 0) (h : n / 100 = 120 / 360) :
    n = 33 + 1 / 3 := by
  have eq1 : n = 100 * (120 / 360) := by
    linarith
  rw [eq1]
  norm_num