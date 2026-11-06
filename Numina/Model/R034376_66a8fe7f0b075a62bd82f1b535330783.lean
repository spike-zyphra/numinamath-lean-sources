import Mathlib

theorem algebra_180621 (x : ℝ) (hx : x = 1.08 * 1.11 * 1.09 * 1.12) :
    x > 1.4:= by
  rw [hx]
  norm_num