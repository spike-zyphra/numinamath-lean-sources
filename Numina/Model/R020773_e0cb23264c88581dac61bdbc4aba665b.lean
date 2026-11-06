import Mathlib

theorem algebra_199766 (x y z : ℝ) (h : x^2 + y^2 + z^2 = 3*x + 8*y + z) :
    x^2 + y^2 + z^2 ≤ 74 := by
  nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 8), sq_nonneg (z - 1),
          sq_nonneg (x - 3/2), sq_nonneg (y - 4), sq_nonneg (z - 1/2),
          h]