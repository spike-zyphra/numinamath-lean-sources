import Mathlib

open Real

theorem inequalities_221557 (x y : ℝ) (h : 3 * x ^ 2 + 2 * y ^ 2 ≤ 6) :
    2 * x + y ≤ sqrt 11 := by
  have h1 : (2 * x + y) ^ 2 ≤ 11 := by
    nlinarith [sq_nonneg (x - 4 * Real.sqrt 11 / 11), sq_nonneg (y - 3 * Real.sqrt 11 / 11), 
          sq_nonneg (x + 4 * Real.sqrt 11 / 11), sq_nonneg (y + 3 * Real.sqrt 11 / 11), 
          Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
  have h2 : 2 * x + y ≤ Real.sqrt 11 := by
    have h3 : (2 * x + y) ^ 2 ≤ 11 := h1
    have h4 : (2 * x + y) ≤ Real.sqrt 11 := by
      nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num), 
           sq_nonneg (Real.sqrt 11 - (2 * x + y))]
    linarith
  linarith