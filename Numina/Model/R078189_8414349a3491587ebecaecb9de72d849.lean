import Mathlib

theorem algebra_20625 : (-Real.sqrt 3 + Real.sqrt 5 + Real.sqrt 6 + Real.sqrt 7)^2 + (Real.sqrt 3 - Real.sqrt 5 + Real.sqrt 6 + Real.sqrt 7)^2 + (Real.sqrt 3 + Real.sqrt 5 - Real.sqrt 6 + Real.sqrt 7)^2 + (Real.sqrt 3 + Real.sqrt 5 + Real.sqrt 6 - Real.sqrt 7)^2 = 84 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num),
    Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, Real.sqrt_nonneg 6, Real.sqrt_nonneg 7]