import Mathlib

theorem inequalities_81125 (x y : ℝ) (h : x ^ 2 + x ≤ y) : y ^ 2 + y ≥ x := by
  nlinarith [sq_nonneg (y - x), sq_nonneg (x + 1/2), sq_nonneg (y + 1/2), sq_nonneg (y - x^2 - x)]