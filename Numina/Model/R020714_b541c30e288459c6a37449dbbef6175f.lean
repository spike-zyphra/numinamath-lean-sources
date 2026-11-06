import Mathlib

theorem algebra_249037 (p1 p2 q1 q2 : ℝ) (h : p1 * p2 = 2 * (q1 + q2)) :
    ∃ x : ℝ, x ^ 2 + p1 * x + q1 = 0 ∨ x ^ 2 + p2 * x + q2 = 0 := by 
  by_cases h1 : p1 ^ 2 - 4 * q1 ≥ 0
  · use (-p1 + Real.sqrt (p1 ^ 2 - 4 * q1)) / 2
    left
    nlinarith [Real.sqrt_nonneg (p1 ^ 2 - 4 * q1), Real.sq_sqrt (show 0 ≤ (p1 ^ 2 - 4 * q1 : ℝ) by linarith)]
  · -- Now, if p1 ^ 2 - 4 * q1 < 0, we need p2 ^ 2 - 4 * q2 ≥ 0
    have h2 : p2 ^ 2 - 4 * q2 ≥ 0 := by 
      nlinarith [show (p1 - p2) ^ 2 ≥ 0 by nlinarith, h, sq_nonneg (p1 - p2), sq_nonneg (p1 + p2)]
    use (-p2 + Real.sqrt (p2 ^ 2 - 4 * q2)) / 2 
    right 
    nlinarith [Real.sqrt_nonneg (p2 ^ 2 - 4 * q2), Real.sq_sqrt (show 0 ≤ (p2 ^ 2 - 4 * q2 : ℝ) by linarith)]