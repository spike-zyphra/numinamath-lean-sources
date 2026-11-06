import Mathlib

open Real Set

theorem algebra_218280 (x y : ℝ) (hx : 1 < x) (hy : 1 < y)
    (h : x * y - 2 * x - y + 1 = 0) :
    3 / 2 * x ^ 2 + y ^ 2 ≥ 15 := by
  nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 3),
          sq_nonneg (x - 2), sq_nonneg (y - 3),
          mul_pos (sub_pos.mpr hx) (sub_pos.mpr (show 1 < y by linarith)), 
          sq_nonneg (x * y - 2 * x - y + 1)]