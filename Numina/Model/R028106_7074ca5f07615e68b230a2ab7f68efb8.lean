import Mathlib

open Real

theorem inequalities_224645 (a b c : ℝ) (h : a^2 * b * c + a * b^2 * c + a * b * c^2 = 1) :
    a^2 + b^2 + c^2 ≥ sqrt 3 := by
  nlinarith [sq_nonneg (a^2 + b^2 + c^2 - sqrt 3), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), 
          sq_nonneg (a * b + b * c + c * a - sqrt 3 / 2), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          Real.sqrt_nonneg 3, 
          sq_nonneg (a * b * c), 
          sq_nonneg (a + b + c), 
          sq_nonneg (a * b * c * (a + b + c) - 1 / 3), 
          sq_nonneg ((a^2 + b^2 + c^2 : ℝ) ^ 2 - 3) 
        ]