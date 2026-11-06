import Mathlib

theorem inequalities_127112 (x y z : ℝ) (h : 2 * x + y ^ 2 + z ^ 2 ≤ 2) :
    x + y + z ≤ 2 := by
  nlinarith [sq_nonneg (y - z), sq_nonneg (y + z - 2), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]