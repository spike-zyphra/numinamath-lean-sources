import Mathlib

open Real Set

theorem algebra_132032 (x y : ℝ) :
    (2 * x + sqrt 2 * y) / (2 * x ^ 4 + 4 * y ^ 4 + 9) ≤ 1 / 4 := by
  have h1 : 0 < (2 * x ^ 4 + 4 * y ^ 4 + 9 : ℝ) := by
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (y ^ 2), sq_nonneg (x * 2), sq_nonneg (y * 2)]
  have h2 : 4 * (2 * x + sqrt 2 * y) ≤ 2 * x ^ 4 + 4 * y ^ 4 + 9 := by
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1 / 2), 
          sq_nonneg (x ^ 2 - 2), sq_nonneg (y ^ 2 - 1 / 4),
          sq_nonneg (x - 1), sq_nonneg (y - Real.sqrt 2 / 2),
          sq_nonneg (Real.sqrt 2 * x - 2 * y),
          sq_nonneg (2 * x ^ 2 - Real.sqrt 2 * y ^ 2 * 2),
          Real.sqrt_nonneg 2, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          sq_nonneg (2 * x - Real.sqrt 2 * 2 / 2),
          sq_nonneg (Real.sqrt 2 * y - (Real.sqrt 2 / 2 * Real.sqrt 2)), 
          sq_nonneg (x ^ 2 - 2 * y ^ 2)]
  have h4 : 0 < (2 * x ^ 4 + 4 * y ^ 4 + 9 : ℝ) := by
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (y ^ 2), sq_nonneg (x * 2), sq_nonneg (y * 2)]
  apply (div_le_iff₀ h4).mpr
  linarith