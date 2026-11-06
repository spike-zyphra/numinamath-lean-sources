import Mathlib

theorem algebra_318532 {a b c : ℝ} (h : (c - a)^2 - 4 * (a - b) * (b - c) = 0) :
    b - a = c - b := by
  nlinarith [sq_nonneg (c - b - (b - a)), sq_nonneg (a - 2 * b + c)]