import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_303082 (a b : ℝ) (h : a + b = 1) :
    3 * sqrt (1 + 2 * a ^ 2) + 2 * sqrt (40 + 9 * b ^ 2) ≥ 5 * sqrt 11 := by
  have h1 : b = 1 - a := by
    linarith
  rw [h1] at *
  have h2 : 3 * sqrt (1 + 2 * a ^ 2) + 2 * sqrt (40 + 9 * (1 - a) ^ 2) ≥ 5 * sqrt 11 := by
    have h3 : 3 * sqrt (1 + 2 * a ^ 2) + 2 * sqrt (40 + 9 * (1 - a) ^ 2) ≥ 0 := by
      positivity
    have h4 : (5 * sqrt 11) ≥ 0 := by
      positivity
    have h5 : (3 * sqrt (1 + 2 * a ^ 2) + 2 * sqrt (40 + 9 * (1 - a) ^ 2)) ^ 2 ≥ (5 * sqrt 11) ^ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 + 2 * a ^ 2 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (40 + 9 * (1 - a) ^ 2 : ℝ) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num), sq_nonneg (sqrt (1 + 2 * a ^ 2) ), sq_nonneg (sqrt (40 + 9 * (1 - a) ^ 2) ), sq_nonneg (sqrt (11 : ℝ) ), mul_nonneg (Real.sqrt_nonneg (1 + 2 * a ^ 2)) (Real.sqrt_nonneg (40 + 9 * (1 - a) ^ 2)), Real.sqrt_nonneg (1 + 2 * a ^ 2), Real.sqrt_nonneg (40 + 9 * (1 - a) ^ 2), Real.sqrt_nonneg (11 : ℝ), sq_nonneg (a - 2 / 3), sq_nonneg ((1 - a : ℝ) - 2 / 3), sq_nonneg ((a : ℝ) - (1 - a : ℝ)), Real.sqrt_nonneg (11 : ℝ)]
    nlinarith [Real.sqrt_nonneg (1 + 2 * a ^ 2), Real.sqrt_nonneg (40 + 9 * (1 - a) ^ 2), Real.sqrt_nonneg (11), h5, h3, h4, Real.sq_sqrt (show (0 : ℝ) ≤ 1 + 2 * a ^ 2 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (40 + 9 * (1 - a) ^ 2 : ℝ) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num), sq_nonneg (a - 4 / 9), sq_nonneg ((a : ℝ) - (1 - a : ℝ)), sq_nonneg ((1 - a) - 2 / 3), sq_nonneg (a * (1 - a)), h1, Real.sqrt_nonneg (11 : ℝ)]
  linarith [h2]