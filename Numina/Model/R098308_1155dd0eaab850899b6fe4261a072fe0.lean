import Mathlib

theorem algebra_309738 {a : ℝ} (ha : a = Real.sqrt 7 - 1) : 3 * a^3 + 12 * a^2 - 6 * a - 12 = 24 := by
  rw [ha]
  have h1 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (show (7 : ℝ) ≥ 0 by norm_num)
  nlinarith [Real.sqrt_nonneg 7, sq_nonneg (Real.sqrt 7 - 2), sq_nonneg (Real.sqrt 7 - 4), 
          Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), 
          sq_nonneg (Real.sqrt 7 ^ 2 - 7)]