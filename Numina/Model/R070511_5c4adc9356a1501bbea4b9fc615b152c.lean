import Mathlib

theorem inequalities_155525 (x1 x2 x3 : ℝ) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3)
    (hsum : x1 + x2 + x3 ≤ 1 / 2) :
    (1 - x1) * (1 - x2) * (1 - x3) ≥ 1 / 2 := by
  nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 - x3), sq_nonneg (x2 - x3), 
          mul_nonneg hx1 hx2, mul_nonneg hx1 hx3, mul_nonneg hx2 hx3, 
          mul_nonneg (show (0 : ℝ) ≤ 1 - x1 by nlinarith) (show (0 : ℝ) ≤ 1 - x2 by nlinarith), 
          mul_nonneg (show (0 : ℝ) ≤ 1 - x1 by nlinarith) (show (0 : ℝ) ≤ 1 - x3 by nlinarith), 
          mul_nonneg (show (0 : ℝ) ≤ 1 - x2 by nlinarith) (show (0 : ℝ) ≤ 1 - x3 by nlinarith)]