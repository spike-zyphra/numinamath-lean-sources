import Mathlib

theorem inequalities_8135 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h : x ^ 3 + y ^ 3 = x - y) : x ^ 2 + y ^ 2 < 1 := by
  nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1), sq_nonneg (x - y),
          sq_nonneg (x + y - 1), sq_nonneg (x * y - y), sq_nonneg (x * y - x),
          mul_pos hx hy, sq_nonneg (x - 1), sq_nonneg (y - 1), 
          sq_nonneg (x ^ 2 + y ^ 2 - 1)]