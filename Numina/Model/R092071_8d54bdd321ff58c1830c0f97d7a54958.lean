import Mathlib

theorem inequalities_276866 (x : ℝ) : 1 + 2 * x ^ 4 ≥ x ^ 2 + 2 * x ^ 3 := by 
  nlinarith [sq_nonneg (x ^ 2 - x), sq_nonneg (x - 1), 
    sq_nonneg (2 * x ^ 2 + 2 * x + 1), sq_nonneg (x * (x - 1)), 
    sq_nonneg (x + 1), sq_nonneg (x - 2)]