import Mathlib

open Real

theorem inequalities_101004 (x : ℝ) (hx : 3/2 ≤ x ∧ x ≤ 5) :
    2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x) < 2 * sqrt 19 := by
  have h1 : 3 / 2 ≤ x := hx.1
  have h2 : x ≤ 5 := hx.2
  have h3 : 0 ≤ (x + 1 : ℝ) := by linarith
  have h4 : 0 ≤ (2 * x - 3 : ℝ) := by nlinarith
  have h5 : 0 ≤ (15 - 3 * x : ℝ) := by nlinarith
  have h6 : (2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x)) ^ 2 < (2 * sqrt 19 ) ^ 2 := by
    nlinarith [sq_nonneg (2 * sqrt (x + 1) - sqrt (2 * x - 3) - sqrt (15 - 3 * x)), sq_nonneg (sqrt (2 * x - 3) - sqrt (15 - 3 * x)), sq_nonneg (sqrt (x + 1) - sqrt (2 * x - 3)), sq_nonneg (sqrt (x + 1) - sqrt (15 - 3 * x)), Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (2 * x - 3), Real.sqrt_nonneg (15 - 3 * x), Real.sqrt_nonneg (19 : ℝ), Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (x + 1 : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (2 * x - 3 : ℝ) by nlinarith), Real.sq_sqrt (show 0 ≤ (15 - 3 * x : ℝ) by nlinarith), mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (2 * x - 3)), mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (15 - 3 * x)), mul_nonneg (Real.sqrt_nonneg (2 * x - 3)) (Real.sqrt_nonneg (15 - 3 * x)), Real.sqrt_le_sqrt (by nlinarith : (x + 1 : ℝ) ≤ (19 : ℝ)), Real.sqrt_le_sqrt (by nlinarith : (2 * x - 3 : ℝ) ≤ (19 : ℝ)), Real.sqrt_le_sqrt (by nlinarith : (15 - 3 * x : ℝ) ≤ (19 : ℝ))]
  have h7 : 2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x) ≥ 0 := by
    positivity
  have h8 : 2 * sqrt 19 ≥ 0 := by
    positivity
  nlinarith [h7, h8, h6, Real.sqrt_nonneg (19 : ℝ), Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (2 * x - 3), Real.sqrt_nonneg (15 - 3 * x)]