import Mathlib

open Real Set

theorem inequalities_327562 (x y : ℝ) (h : x^2 + 3 * x * y + 4 * y^2 ≤ 7 / 2) : x + y ≤ 2 := by
  nlinarith [sq_nonneg (x + y - 2), sq_nonneg (y), sq_nonneg (x - 2 * y), sq_nonneg (x + 5 * y), sq_nonneg (x - y)]