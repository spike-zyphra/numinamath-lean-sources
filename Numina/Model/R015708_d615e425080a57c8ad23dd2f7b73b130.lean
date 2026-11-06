import Mathlib

open Real

theorem inequalities_48907 (a b : ℝ) (h : a + b = 1) :
    sqrt (1 + 5 * a ^ 2) + 5 * sqrt (2 + b ^ 2) ≥ 9 := by
  have h1 : b = 1 - a := by linarith
  rw [h1]
  have h3 : (sqrt (1 + 5 * a ^ 2) + 5 * sqrt (2 + (1 - a) ^ 2)) ^ 2 ≥ 81 := by
    have h10 : (sqrt (1 + 5 * a ^ 2)) ^ 2 = 1 + 5 * a ^ 2 := by 
      rw [Real.sq_sqrt]
      nlinarith
    have h11 : (5 * sqrt (2 + (1 - a) ^ 2)) ^ 2 = 25 * (2 + (1 - a) ^ 2) := by 
      calc
        (5 * sqrt (2 + (1 - a) ^ 2)) ^ 2 = 25 * (sqrt (2 + (1 - a) ^ 2) ^ 2) := by ring
        _ = 25 * (2 + (1 - a) ^ 2) := by
          rw [Real.sq_sqrt]
          nlinarith
    have h12 : 10 * (sqrt (1 + 5 * a ^ 2) * (sqrt (2 + (1 - a) ^ 2))) ≥ 5 + 50 * a - 30 * a ^ 2 := by 
      nlinarith [sq_nonneg (sqrt (1 + 5 * a ^ 2) - 5 * sqrt (2 + (1 - a) ^ 2)), sq_nonneg (a - 2 / 3), sq_nonneg ((1 - a) - 1 / 3), Real.sqrt_nonneg (1 + 5 * a ^ 2), Real.sqrt_nonneg (2 + (1 - a) ^ 2), mul_nonneg (Real.sqrt_nonneg (1 + 5 * a ^ 2)) (Real.sqrt_nonneg (2 + (1 - a) ^ 2)), Real.sq_sqrt (show 0 ≤ (1 + 5 * a ^ 2 : ℝ) by nlinarith), Real.sq_sqrt (show 0 ≤ (2 + (1 - a) ^ 2 : ℝ) by nlinarith), sq_nonneg (sqrt (1 + 5 * a ^ 2) - sqrt (2 + (1 - a) ^ 2))]
    nlinarith [h10, h11, h12, Real.sqrt_nonneg (1 + 5 * a ^ 2), Real.sqrt_nonneg (2 + (1 - a) ^ 2), sq_nonneg (sqrt (1 + 5 * a ^ 2) - 5 * sqrt (2 + (1 - a) ^ 2)), sq_nonneg (sqrt (1 + 5 * a ^ 2) - 2), sq_nonneg (sqrt (2 + (1 - a) ^ 2) - 1)]
  have h4 : sqrt (1 + 5 * a ^ 2) + 5 * sqrt (2 + (1 - a) ^ 2) ≥ 9 := by 
    nlinarith [Real.sqrt_nonneg (1 + 5 * a ^ 2), Real.sqrt_nonneg (2 + (1 - a) ^ 2), h3, mul_nonneg (Real.sqrt_nonneg (1 + 5 * a ^ 2)) (Real.sqrt_nonneg (2 + (1 - a) ^ 2)), sq_nonneg (sqrt (1 + 5 * a ^ 2) - 5 * sqrt (2 + (1 - a) ^ 2))]
  exact h4