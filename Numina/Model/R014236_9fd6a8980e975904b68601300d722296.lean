import Mathlib

theorem algebra_7354 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : 4 * x * y * (x - 1) * (y - 4) + 20 * x * (x - 1) + 2 * y * (y - 4) + 9 = 0) :
    x + y = 5 / 2 := by
  nlinarith [sq_nonneg (2 * x - 1), sq_nonneg (y - 2), sq_nonneg (x - 1), sq_nonneg (y - 4),
          sq_nonneg ((2 * x - 1) - (y - 2)), sq_nonneg ((2 * x - 1) + (y - 2)), sq_nonneg (4 * x * (y - 4)), sq_nonneg ((x - 1) * (y - 4)), 
          mul_pos hx hy]