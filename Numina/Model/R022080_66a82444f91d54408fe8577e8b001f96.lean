import Mathlib

theorem calculus_59863 (t : ℝ) (ht : t > 0) (h : 10 * t + 8 * t = 3) :
    15 * t = 5 / 2 := by
  have eq1 : t = 1 / 6 := by
    linarith
  rw [eq1]
  norm_num