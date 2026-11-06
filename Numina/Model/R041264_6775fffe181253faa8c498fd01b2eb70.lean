import Mathlib

open Real Set

theorem algebra_310891 (x y : ℝ) (h : 3 * x ^ 2 + 2 * y ^ 2 = 6 * x) :
    5 / 2 - 3 * sqrt 6 ≤ 2 * x ^ 2 + 3 * y ^ 2 - 4 * x - 6 * y ∧
    2 * x ^ 2 + 3 * y ^ 2 - 4 * x - 6 * y ≤ 5 / 2 + 3 * sqrt 6 := by
  have h1 : 2 * x ^ 2 + 3 * y ^ 2 - 4 * x - 6 * y = 2 * (x - 1) ^ 2 + 3 * (y - 1) ^ 2 - 5 := by
    nlinarith
  have h2 : 3 * (x - 1) ^ 2 + 2 * y ^ 2 = 3 := by
    nlinarith
  constructor
  · -- Prove lower bound
    nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
      Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg ((x - 1) - 1), sq_nonneg (y - 0), sq_nonneg (3 * (x - 1) ^ 2 - 2 * y ^ 2), sq_nonneg ((Real.sqrt 6) * (x - 1) - (y)), Real.sqrt_nonneg (6)]
  · -- Prove upper bound
    nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
      Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg ((x - 1) - 1), sq_nonneg (y - 0), sq_nonneg (3 * (x - 1) ^ 2 - 2 * y ^ 2), sq_nonneg ((Real.sqrt 6) * (x - 1) + (y)), Real.sqrt_nonneg (6)]