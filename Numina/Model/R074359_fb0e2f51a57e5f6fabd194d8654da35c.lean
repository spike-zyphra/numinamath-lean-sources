import Mathlib

theorem inequalities_107541 (x : ℝ) (hx : x > 0) :
    1 + x + x^2 + x^3 + x^4 ≥ 5 * x^2 := by
  nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x ^ 2 - x), sq_nonneg (x ^ 2 - 2 * x)]