import Mathlib

open Real

theorem inequalities_829 (a : ℝ) : a + a^3 - a^4 - a^6 < √2 / 2 := by
  nlinarith [sq_nonneg (a^2 - 1/2), sq_nonneg (a^2 - 1), sq_nonneg (a - 1/2), sq_nonneg (a + 1/2),
          sq_nonneg (a^2), sq_nonneg (a^3), sq_nonneg (a - √2 / 2), sq_nonneg (a + √2 / 2),
          Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
          sq_nonneg (a^2 - (√2 / 2)^2), sq_nonneg (a - 1), sq_nonneg (a + 1),
          sq_nonneg (a^2 - a), sq_nonneg (a^2 + a)]