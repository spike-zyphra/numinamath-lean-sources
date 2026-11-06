import Mathlib

theorem inequalities_297760 (a b c : ℝ) : (a^2 + b^2 + c^2) / 3 ≥ (a + b + c) ^ 2 / 9 := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c)]