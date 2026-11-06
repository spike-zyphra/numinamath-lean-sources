import Mathlib

theorem algebra_187939 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x + y ^ 2 = x * y) :
    x ≥ 4 := by
  nlinarith [sq_nonneg (y - 2), sq_nonneg (x - 4), sq_nonneg (y - x / 2), 
          mul_pos hx hy, sq_nonneg (y ^ 2 - 4), sq_nonneg (y * (y - 2) : ℝ)]