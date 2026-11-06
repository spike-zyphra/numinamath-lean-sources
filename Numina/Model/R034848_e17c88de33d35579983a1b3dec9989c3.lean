import Mathlib

theorem algebra_241587 (x y z w : ℝ) (h : x^2 + y^2 + z^2 + w^2 + x + 3 * y + 5 * z + 7 * w = 4) :
    x + y + z + w ≤ 2 := by
  nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1), sq_nonneg (z - 0), sq_nonneg (w + 1),
           sq_nonneg (x + 1/2), sq_nonneg (y + 3/2), sq_nonneg (z + 5/2), sq_nonneg (w + 7/2),
           mul_self_nonneg (x - 2), mul_self_nonneg (y - 1), mul_self_nonneg (z - 0), mul_self_nonneg (w + 1)]