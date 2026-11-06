import Mathlib

theorem algebra_344 (a1 a2 b1 b2 c1 c2 : ℝ)
  (h1 : a1 * c2 - 2 * b1 * b2 + c1 * a2 = 0) (h2 : a1 * c1 - b1 ^ 2 > 0) :
  a2 * c2 - b2 ^ 2 ≤ 0 := by
  nlinarith [sq_nonneg (a1 * b2 - b1 * c2), sq_nonneg (c1 * b2 - b1 * a2), sq_nonneg (a2 * b1 - b2 * c1), sq_nonneg (a1 - c1), sq_nonneg (a2 - c2), sq_nonneg (a1 * a2 - c1 * c2), sq_nonneg (b1 - b2), sq_nonneg (a1 * c2 - c1 * a2), sq_nonneg (b1 * c2 - b2 * c1), sq_nonneg (a1 * c1 - b1 ^ 2), mul_pos h2 (show 0 < a1 * c1 - b1 ^ 2 by linarith)]