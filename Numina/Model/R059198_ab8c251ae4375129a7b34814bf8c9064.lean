import Mathlib

open Real

theorem inequalities_115982 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    sqrt (4 * a + 1) + sqrt (4 * b + 1) + sqrt (4 * c + 1) > 2 + sqrt 5 := by 
  have h6 : sqrt (4 * a + 1) > 1 := by
    have h7 : 4 * a + 1 > 1 := by nlinarith [h]
    have h8 : sqrt (4 * a + 1) > sqrt 1 := Real.sqrt_lt_sqrt (by linarith) (by nlinarith)
    have h9 : sqrt 1 = 1 := Real.sqrt_one
    linarith
  have h7 : sqrt (4 * b + 1) > 1 := by
    have h8 : 4 * b + 1 > 1 := by nlinarith [h]
    have h9 : sqrt (4 * b + 1) > sqrt 1 := Real.sqrt_lt_sqrt (by linarith) (by nlinarith)
    have h10 : sqrt 1 = 1 := Real.sqrt_one
    linarith
  have h8 : sqrt (4 * c + 1) > 1 := by
    have h9 : 4 * c + 1 > 1 := by nlinarith [h]
    have h10 : sqrt (4 * c + 1) > sqrt 1 := Real.sqrt_lt_sqrt (by linarith) (by nlinarith)
    have h11 : sqrt 1 = 1 := Real.sqrt_one
    linarith
  nlinarith [Real.sqrt_nonneg (4 * a + 1), Real.sqrt_nonneg (4 * b + 1), Real.sqrt_nonneg (4 * c + 1),
    Real.sq_sqrt (show 0 ≤ (4 * a + 1 : ℝ) by nlinarith), Real.sq_sqrt (show 0 ≤ (4 * b + 1 : ℝ) by nlinarith), Real.sq_sqrt (show 0 ≤ (4 * c + 1 : ℝ) by nlinarith),
    Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num),
    h6, h7, h8, Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), 
    Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num),
    h]