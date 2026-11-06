import Mathlib

theorem algebra_240268 {a b c d : ℝ} (ha : a ^ 2 + b ^ 2 = 1) (hc : c ^ 2 + d ^ 2 = 1)
    (h : a * c + b * d = 0) : a * b + c * d = 0 := by 
  nlinarith [sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (a + d), sq_nonneg (b + c), 
          sq_nonneg (a * c + b * d), sq_nonneg (a * d - b * c), 
          sq_nonneg (a * b + c * d)]