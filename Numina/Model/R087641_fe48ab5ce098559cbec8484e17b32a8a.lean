import Mathlib

theorem algebra_245982 (x : ℝ) (hx : x = 6000) :
    (1000 * 0.06 + (x - 1000) * 0.05) = 310 := by
  rw [hx]
  norm_num