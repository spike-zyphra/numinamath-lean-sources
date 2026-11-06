import Mathlib

open Real

theorem inequalities_210328 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    sqrt (4 * a + 1) + sqrt (4 * b + 1) + sqrt (4 * c + 1) + sqrt (4 * d + 1) < 6 := by

  have h1 : sqrt (4 * a + 1) < 2 * a + 1 := by
    have h2 : 0 < (4 * a + 1 : ℝ) := by nlinarith
    have h3 : sqrt (4 * a + 1) < 2 * a + 1 := by
      nlinarith [Real.sqrt_nonneg (4 * a + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (4 * a + 1 : ℝ) by nlinarith), sq_pos_of_pos ha]
    linarith

  have h2 : sqrt (4 * b + 1) < 2 * b + 1 := by
    have h4 : 0 < (4 * b + 1 : ℝ) := by nlinarith
    have h5 : sqrt (4 * b + 1) < 2 * b + 1 := by
      nlinarith [Real.sqrt_nonneg (4 * b + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (4 * b + 1 : ℝ) by nlinarith), sq_pos_of_pos hb]
    linarith

  have h3 : sqrt (4 * c + 1) < 2 * c + 1 := by
    have h4 : 0 < (4 * c + 1 : ℝ) := by nlinarith
    have h5 : sqrt (4 * c + 1) < 2 * c + 1 := by
      nlinarith [Real.sqrt_nonneg (4 * c + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (4 * c + 1 : ℝ) by nlinarith), sq_pos_of_pos hc]
    linarith

  have h4 : sqrt (4 * d + 1) < 2 * d + 1 := by
    have h5 : 0 < (4 * d + 1 : ℝ) := by nlinarith
    have h6 : sqrt (4 * d + 1) < 2 * d + 1 := by
      nlinarith [Real.sqrt_nonneg (4 * d + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (4 * d + 1 : ℝ) by nlinarith), sq_pos_of_pos hd]
    linarith

  have h5 : sqrt (4 * a + 1) + sqrt (4 * b + 1) + sqrt (4 * c + 1) + sqrt (4 * d + 1) < (2 * a + 1) + (2 * b + 1) + (2 * c + 1) + (2 * d + 1) := by
    linarith [h1, h2, h3, h4]

  have h6 : (2 * a + 1) + (2 * b + 1) + (2 * c + 1) + (2 * d + 1) = 6 := by
    nlinarith [h]

  linarith [h5, h6]