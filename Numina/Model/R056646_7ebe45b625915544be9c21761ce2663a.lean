import Mathlib

theorem algebra_117916 {a b : ℝ} (h : (a + b + a) * (a + b + b) = 9) :
    a * b ≤ 1 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1), sq_nonneg (b - 1)]