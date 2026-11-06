import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_185546 (x1 x2 : ℝ) (hx1 : |x1| ≤ 1) (hx2 : |x2| ≤ 1) :
  sqrt (1 - x1^2) + sqrt (1 - x2^2) ≤ 2 * sqrt (1 - ((x1 + x2) / 2)^2) := by 
  have h1 : -1 ≤ x1 ∧ x1 ≤ 1 := by 
    constructor
    · linarith [abs_le.mp hx1]
    · linarith [abs_le.mp hx1]
  have h2 : -1 ≤ x2 ∧ x2 ≤ 1 := by 
    constructor
    · linarith [abs_le.mp hx2]
    · linarith [abs_le.mp hx2]
  have h3 : 1 - x1 ^ 2 ≥ 0 := by nlinarith
  have h4 : 1 - x2 ^ 2 ≥ 0 := by nlinarith
  have h5 : 1 - ((x1 + x2) / 2) ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 + x2), h1.1, h1.2, h2.1, h2.2]

  suffices h : sqrt (1 - x1^2) + sqrt (1 - x2^2) ≤ 2 * sqrt (1 - ((x1 + x2) / 2)^2) by 
    exact h
  
  have h6 : (sqrt (1 - x1 ^ 2) + sqrt (1 - x2 ^ 2)) ^ 2 ≤ (2 * sqrt (1 - ((x1 + x2) / 2) ^ 2)) ^ 2 := by
    nlinarith [sq_nonneg (sqrt (1 - x1 ^ 2) - sqrt (1 - x2 ^ 2)), sq_nonneg (sqrt (1 - ((x1 + x2) / 2) ^ 2)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x1 ^ 2 by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x2 ^ 2 by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 1 - ((x1 + x2) / 2) ^ 2 by linarith),
          mul_nonneg (Real.sqrt_nonneg (1 - x1 ^ 2)) (Real.sqrt_nonneg (1 - x2 ^ 2)), 
          mul_nonneg (Real.sqrt_nonneg (1 - ((x1 + x2) / 2) ^ 2)) (Real.sqrt_nonneg (1 - ((x1 + x2) / 2) ^ 2)), 
          Real.sqrt_nonneg (1 - x1 ^ 2), Real.sqrt_nonneg (1 - x2 ^ 2), Real.sqrt_nonneg (1 - ((x1 + x2) / 2) ^ 2), 
          sq_nonneg (sqrt (1 - x1 ^ 2) + sqrt (1 - x2 ^ 2)), sq_nonneg (sqrt (1 - ((x1 + x2) / 2) ^ 2)), 
          sq_nonneg (x1 - x2), sq_nonneg (x1 + x2), 
          h1.1, h1.2, h2.1, h2.2 ]
  
  have h7 : 0 ≤ sqrt (1 - x1 ^ 2) + sqrt (1 - x2 ^ 2) := by 
    positivity
  have h8 : 0 ≤ 2 * sqrt (1 - ((x1 + x2) / 2) ^ 2) := by
    positivity
  
  nlinarith [h6, h7, h8, Real.sqrt_nonneg (1 - x1 ^ 2), Real.sqrt_nonneg (1 - x2 ^ 2), Real.sqrt_nonneg (1 - ((x1 + x2) / 2) ^ 2)]