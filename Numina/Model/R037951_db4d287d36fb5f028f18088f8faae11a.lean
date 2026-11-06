import Mathlib

theorem inequalities_597925 (x1 x2 : ℝ) (h : x1^2 + x2^2 ≤ 1) (y1 y2 : ℝ) :
    (x1 * y1 + x2 * y2 - 1)^2 ≥ (x1^2 + x2^2 - 1) * (y1^2 + y2^2 - 1) := by 
  nlinarith [sq_nonneg (x1 * y1 + x2 * y2 - (x1^2 + x2^2)), 
            sq_nonneg (x1 - y1), sq_nonneg (x2 - y2), 
            sq_nonneg (x1 + y1), sq_nonneg (x2 + y2),
            sq_nonneg (x1 * y2 - x2 * y1), 
            sq_nonneg ((x1^2 + x2^2) - 1), 
            sq_nonneg ((y1^2 + y2^2) - 1), 
            h, 
            mul_nonneg (show (0 : ℝ) ≤ 1 - (x1 ^2 + x2 ^ 2) by linarith) (show (0 : ℝ) ≤ 1 by linarith)
          ]