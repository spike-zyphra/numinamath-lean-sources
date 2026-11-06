import Mathlib

theorem algebra_131690 (a b c d : ℝ) :
    a^2 + b^2 + c^2 + d^2 + a * b + a * c + a * d + b * c + b * d + c * d + a + b + c + d ≥
    -2 / 5 := by
  nlinarith [sq_nonneg (a + b + c + d + 4/5), 
            sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), 
            sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
            sq_nonneg (a + 1/5), sq_nonneg (b + 1/5), sq_nonneg (c + 1/5), sq_nonneg (d + 1/5)]