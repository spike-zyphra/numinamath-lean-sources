import Mathlib

theorem algebra_123053 {p q : ℝ} (h : (999^2 + p * 999 + q) < 0) (h' : (1001^2 + p * 1001 + q) < 0) :
    p^2 - 4 * q > 4 := by
  nlinarith [sq_pos_of_pos (show (1001:ℝ) - 999 > 0 by norm_num), sq_nonneg (p + 2000), sq_nonneg (q - 999 * (p + 2000)), sq_nonneg ((999:ℝ) * (1001:ℝ) - q), sq_nonneg ((999 +1001 + p):ℝ), sq_nonneg ((1001 - 999):ℝ)]