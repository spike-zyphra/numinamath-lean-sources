import Mathlib

open Real

theorem algebra_7252 : sqrt (3 + 2 * sqrt 2) + sqrt (3 - 2 * sqrt 2) = 2 * sqrt 2 := by 
  have h1 : sqrt (3 + 2 * sqrt 2) = sqrt 2 + 1 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h2 : sqrt (3 - 2 * sqrt 2) = sqrt 2 - 1 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), show 1 < sqrt 2 by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]]
  rw [h1, h2]
  ring