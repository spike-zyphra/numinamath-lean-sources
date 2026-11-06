import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_28410 (x : ℝ) (hx : 1 ≤ x) (hx' : -9 ≤ 2 * x) (hx'' : 3 * x - 19 ≤ 0) :
    sqrt (x - 1) + sqrt (2 * x + 9) + sqrt (19 - 3 * x) < 9 := by
  have h1 : 0 ≤ x - 1 := by linarith
  have h2 : 0 ≤ 2 * x + 9 := by linarith
  have h3 : 0 ≤ 19 - 3 * x := by linarith
  nlinarith [Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (2 * x + 9), Real.sqrt_nonneg (19 - 3 * x),
    sq_nonneg (sqrt (x - 1) - 2), sq_nonneg (sqrt (2 * x + 9) - 4), sq_nonneg (sqrt (19 - 3 * x) - 3),
    Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith), 
    Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x + 9 : ℝ) by linarith), 
    Real.sq_sqrt (show (0 : ℝ) ≤ (19 - 3 * x : ℝ) by linarith), 
    sq_nonneg (x - 19 / 3), sq_nonneg (x - 1)]