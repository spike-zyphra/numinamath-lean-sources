import Mathlib

theorem inequalities_316860 (x y : ℝ) :
    x^2 + x * y + y^2 + 2 * x - 2 * y + 4 ≥ 0 := by
  nlinarith [sq_nonneg (x + (y + 2) / 2), sq_nonneg (y - 2), sq_nonneg (x - y + 6), sq_nonneg (x + y - 2)]