import Mathlib

theorem algebra_171206 {x y : ℝ} (h : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 1) : x + y = 0 := by 
  have h1 : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 1 := h
  have h2 : (x - Real.sqrt (x ^ 2 + 1)) * (y - Real.sqrt (y ^ 2 + 1)) = 1 := by
    have h3 : (x + Real.sqrt (x ^ 2 + 1)) * (x - Real.sqrt (x ^ 2 + 1)) = -1 := by
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show (x ^ 2 + 1 : ℝ) ≥ 0 by nlinarith), Real.sq_sqrt (show (y ^ 2 + 1 : ℝ) ≥ 0 by nlinarith)]
    have h4 : (y + Real.sqrt (y ^ 2 + 1)) * (y - Real.sqrt (y ^ 2 + 1)) = -1 := by
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show (x ^ 2 + 1 : ℝ) ≥ 0 by nlinarith), Real.sq_sqrt (show (y ^ 2 + 1 : ℝ) ≥ 0 by nlinarith)]
    nlinarith [h3, h4, h, Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show (x ^ 2 + 1 : ℝ) ≥ 0 by nlinarith), Real.sq_sqrt (show (y ^ 2 + 1 : ℝ) ≥ 0 by nlinarith), sq_nonneg (x - y), sq_nonneg (x + y)]
  have eq3' : x * Real.sqrt (y ^ 2 + 1) + y * Real.sqrt (x ^ 2 + 1) = 0 := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show (x ^ 2 + 1 : ℝ) ≥ 0 by nlinarith), Real.sq_sqrt (show (y ^ 2 + 1 : ℝ) ≥ 0 by nlinarith), h, h2]
  have h32 : x + y = 0 := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1), 
      sq_nonneg (Real.sqrt (x^2 + 1) - Real.sqrt (y^2 + 1)), 
      mul_nonneg (Real.sqrt_nonneg (x^2 + 1)) (Real.sqrt_nonneg (y^2 + 1)), 
      Real.sq_sqrt (show (x ^ 2 + 1 : ℝ) ≥ 0 by nlinarith), 
      Real.sq_sqrt (show (y ^ 2 + 1 : ℝ) ≥ 0 by nlinarith)]
  linarith