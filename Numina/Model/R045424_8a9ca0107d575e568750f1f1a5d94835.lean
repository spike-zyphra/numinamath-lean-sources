import Mathlib

theorem inequalities_106272 (x : ℝ) (hx : x > 0) :
    1 + x + x^2 + x^3 + x^4 ≥ 5 * x^2 := by
  nlinarith [sq_nonneg (x ^ 2 - x), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 2), sq_nonneg (x - 2),
          sq_nonneg (x + 1), sq_nonneg (x ^ 2 - 1),
          mul_pos hx hx, mul_pos (show 0 < x by linarith) (show 0 < x ^ 2 by positivity)]