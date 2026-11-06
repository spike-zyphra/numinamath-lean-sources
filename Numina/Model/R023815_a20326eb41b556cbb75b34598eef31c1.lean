import Mathlib

theorem algebra_37453 (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 - a * b - b * c - c * d - d + 2 / 5 = 0) :
    a = 1 / 5 := by
  nlinarith [sq_nonneg (a - 1 / 5), sq_nonneg (b - 2 / 5), sq_nonneg (c - 3 / 5), sq_nonneg (d - 4 / 5),
          sq_nonneg (a - b + 1 / 5), sq_nonneg (b - c + 1 / 5), sq_nonneg (c - d + 1 / 5), sq_nonneg (d - 1 / 2)]