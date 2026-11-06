import Mathlib

theorem algebra_120626 (a b c : ℝ) :
    ∃ x, (x - a) * (x - b) + (x - b) * (x - c) + (x - c) * (x - a) = 0 := by
  use (a + b + c + Real.sqrt ((a + b + c) ^ 2 - 3 * (a * b + b * c + c * a)) ) / 3
  nlinarith [Real.sqrt_nonneg ((a + b + c) ^ 2 - 3 * (a * b + b * c + c * a)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a + b + c) ^ 2 - 3 * (a * b + b * c + c * a) by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)])]