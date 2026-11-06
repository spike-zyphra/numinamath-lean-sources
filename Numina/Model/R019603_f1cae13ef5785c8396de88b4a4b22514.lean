import Mathlib

theorem inequalities_156622 (x : ℝ) (hx : 3 / 2 ≤ x ∧ x ≤ 5) :
    2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x) < 2 * Real.sqrt 19 := by
  have h1 : 3 / 2 ≤ x := hx.1
  have h2 : x ≤ 5 := hx.2
  have h3 : 0 ≤ x + 1 := by linarith
  have h4 : 0 ≤ 2 * x - 3 := by linarith
  have h5 : 0 ≤ 15 - 3 * x := by linarith
  have h6 : (2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x)) ^ 2 < (2 * Real.sqrt 19) ^ 2 := by
    nlinarith [sq_nonneg (2 * Real.sqrt (x + 1) - Real.sqrt (2 * x - 3) - Real.sqrt (15 - 3 * x)), sq_nonneg (Real.sqrt (x + 1) - Real.sqrt (2 * x - 3)), sq_nonneg (Real.sqrt (x + 1) - Real.sqrt (15 - 3 * x)), sq_nonneg (Real.sqrt (2 * x - 3) - Real.sqrt (15 - 3 * x)), Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (2 * x - 3), Real.sqrt_nonneg (15 - 3 * x), Real.sqrt_nonneg 19, Real.sq_sqrt (show (0 : ℝ) ≤ x + 1 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x - 3 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (15 - 3 * x : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (19 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (2 * x - 3)), mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (15 - 3 * x)), mul_nonneg (Real.sqrt_nonneg (2 * x - 3)) (Real.sqrt_nonneg (15 - 3 * x)), sq_nonneg (2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x) - 2 * Real.sqrt 19), mul_nonneg (show 0 ≤ (x - 3 / 2) by linarith) (show 0 ≤ (5 - x) by linarith)]
  have h7 : 0 ≤ 2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x) := by positivity
  have h8 : 0 ≤ 2 * Real.sqrt 19 := by positivity
  nlinarith [Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (2 * x - 3), Real.sqrt_nonneg (15 - 3 * x), Real.sqrt_nonneg 19]