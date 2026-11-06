import Mathlib
theorem algebra_605812 (a b : ℝ) (h : a * b ≥ a ^ 3 + b ^ 3) :
    a + b ≤ 1 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1)]