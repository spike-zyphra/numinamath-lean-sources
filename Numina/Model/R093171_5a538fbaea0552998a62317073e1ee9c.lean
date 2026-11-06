import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_318214 (v : ℝ) (h : v > 0) :
    (4 + 2 * v) / (2.5 + v) ≤ 2 * sqrt 2 := by 
  have h1 : 0 < (2.5 + v) := by
    have h2 : (2.5 : ℝ) + v > (0 : ℝ) := by
      have h3 : v > (0 : ℝ) := by linarith
      norm_num at *
      linarith
    linarith
  apply (div_le_iff₀ h1).mpr
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  -- Multiply both sides by denominator
  nlinarith [sq_nonneg (sqrt 2 - 1), sq_nonneg (2 - (sqrt 2)), Real.sqrt_pos.mpr (show (2:ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]