import Mathlib

theorem inequalities_120754 (x y : ℝ) :
    x^2 + y^2 + 1 > x * Real.sqrt (y^2 + 1) + y * Real.sqrt (x^2 + 1) := by 
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - Real.sqrt (y^2 + 1)), sq_nonneg (y - Real.sqrt (x^2 + 1)), 
            sq_nonneg (x * y - Real.sqrt (y^2 + 1) * Real.sqrt (x^2 + 1)), 
            Real.sqrt_nonneg (y^2 + 1), Real.sqrt_nonneg (x^2 + 1), 
            mul_nonneg (Real.sqrt_nonneg (y^2 + 1)) (Real.sqrt_nonneg (x^2 + 1)), 
            sq_nonneg (Real.sqrt (y^2 + 1) - Real.sqrt (x^2 + 1)), 
            Real.sq_sqrt (show 0 ≤ (y ^ 2 + 1 : ℝ) by nlinarith), 
            Real.sq_sqrt (show 0 ≤ (x ^ 2 + 1 : ℝ) by nlinarith), 
            sq_nonneg (x - y), sq_nonneg (x + y), 
            mul_self_nonneg (x - y), mul_self_nonneg (x + y)]