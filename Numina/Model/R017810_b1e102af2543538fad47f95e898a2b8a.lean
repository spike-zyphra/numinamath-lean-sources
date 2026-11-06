import Mathlib

theorem algebra_9477 (a b c : ℝ) (h : a^2 + b^2 + c^2 = 1) :
  3*a*b - 3*b*c + 2*c^2 ≤ 3 := by
  nlinarith [sq_nonneg (a - b / 2), sq_nonneg (c + 3 * b / 2), sq_nonneg (a - c), sq_nonneg (b + c), sq_nonneg (a - b), sq_nonneg (b - c)]