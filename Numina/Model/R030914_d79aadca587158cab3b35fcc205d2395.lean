import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_303703 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
  (h : 2 * a + b = 2) :
  sqrt (4 * a ^ 2 + 1) + sqrt (b ^ 2 + 4) ≥ sqrt 13 := by
  have h1 : (sqrt (4 * a ^ 2 + 1) + sqrt (b ^ 2 + 4)) ^ 2 ≥ 13 := by
    have h2 : (sqrt (4 * a ^ 2 + 1) ) ^ 2 = 4 * a ^ 2 + 1 := by
      rw [Real.sq_sqrt]
      positivity
    have h3 : (sqrt (b ^ 2 + 4) ) ^ 2 = b ^ 2 + 4 := by
      rw [Real.sq_sqrt]
      positivity
    have h4 : sqrt (4 * a ^ 2 + 1) * sqrt (b ^ 2 + 4) ≥ 0 := by positivity
    nlinarith [sq_nonneg (2 * a - b / 2), sq_nonneg (b - 4 / 3), sq_nonneg (a - 1 / 3), 
      sq_nonneg (2 * a - 4 / 3), sq_nonneg (b - 4 / 3), 
      Real.sqrt_nonneg (4 * a ^ 2 + 1), Real.sqrt_nonneg (b ^ 2 + 4), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 4 * a ^ 2 + 1 by positivity), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (b ^ 2 + 4 : ℝ) by positivity), 
      mul_nonneg (Real.sqrt_nonneg (4 * a ^ 2 + 1)) (Real.sqrt_nonneg (b ^ 2 + 4)), 
      sq_nonneg ( (sqrt (4 * a ^ 2 + 1)) ^ 2 - (sqrt (b ^ 2 + 4)) ^ 2 ), 
      sq_nonneg ( (2 * a) * 2 - 1 * b ), 
      Real.sqrt_nonneg (13)
    ]
  have h2 : (sqrt (4 * a ^ 2 + 1) + sqrt (b ^ 2 + 4) ) ≥ 0 := by positivity
  have h3 : sqrt 13 ≥ 0 := by positivity
  nlinarith [Real.sqrt_nonneg (13), h1, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), h2, h3]