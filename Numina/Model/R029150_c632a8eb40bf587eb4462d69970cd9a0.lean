import Mathlib

theorem algebra_598561 (x y z u v : ℝ) (h : x + 2 * y + 3 * z + 4 * u + 5 * v = 30) :
    x ^ 2 + 2 * y ^ 2 + 3 * z ^ 2 + 4 * u ^ 2 + 5 * v ^ 2 ≥ 60 := by
  nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2), sq_nonneg (u - 2), sq_nonneg (v - 2),
            h, 
            sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2), sq_nonneg (u - 2), sq_nonneg (v - 2)]