import Mathlib

theorem algebra_123053 {p q : ℝ} (h : (999^2 + p * 999 + q) < 0) (h' : (1001^2 + p * 1001 + q) < 0) :
    p^2 - 4 * q > 4 := by
  nlinarith [sq_nonneg (p + 2 * 999), sq_nonneg (p + 2000)]