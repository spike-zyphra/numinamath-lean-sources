import Mathlib

theorem inequalities_180839 (x : ℝ) :
    x^4 - x^3 + 3 * x^2 - 2 * x + 2 ≥ 0 := by 
  nlinarith [sq_nonneg (x^2 - x/2 + 1), sq_nonneg (x - 1), sq_nonneg (x), sq_nonneg (x^2 - 1)]