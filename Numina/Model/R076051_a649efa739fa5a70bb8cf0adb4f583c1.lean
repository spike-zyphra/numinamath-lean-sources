import Mathlib

theorem algebra_51048 {a b : ℝ} (ha : a^3 - a^2 + a - 5 = 0) (hb : b^3 - 2*b^2 + 2*b + 4 = 0) : a + b = 1 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1), sq_nonneg (a - 1), sq_nonneg (b - 0), sq_nonneg (a + b), sq_nonneg (a - 2), sq_nonneg (b - 1)]