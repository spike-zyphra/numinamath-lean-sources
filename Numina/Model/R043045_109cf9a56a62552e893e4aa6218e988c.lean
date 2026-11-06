import Mathlib

theorem inequalities_200027 (x : ℝ) :
    x^6 + x^5 + 4 * x^4 - 12 * x^3 + 4 * x^2 + x + 1 ≥ 0 := by 
  nlinarith [sq_nonneg (x^2 + x + 1), sq_nonneg (x^2 - 1), sq_nonneg (x - 1), sq_nonneg (x^3 - 1), sq_nonneg (x^2 - x + 1), sq_nonneg (x + 1), sq_nonneg (x^4 + x^2 + 1), sq_nonneg (x^2 - 1), sq_nonneg (x^3 + 1)]