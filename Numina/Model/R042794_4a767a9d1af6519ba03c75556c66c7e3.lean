import Mathlib

theorem algebra_248834 {x y : ℝ} (h : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 1) :
    x + y = 0 := by
  have h1 : Real.sqrt (x ^ 2 + 1) ≥ 0 := by
    apply Real.sqrt_nonneg
  have h2 : Real.sqrt (y ^ 2 + 1) ≥ 0 := by
    apply Real.sqrt_nonneg

  have h5 : (x + Real.sqrt (x ^ 2 + 1)) * (-x + Real.sqrt (x ^ 2 + 1)) = 1 := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 1 by nlinarith)]
  have h6 : (y + Real.sqrt (y ^ 2 + 1)) * (-y + Real.sqrt (y ^ 2 + 1)) = 1 := by
    nlinarith [Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 1 by nlinarith)]
  have h7 : (-x + Real.sqrt (x ^ 2 + 1)) * (-y + Real.sqrt (y ^ 2 + 1)) = 1 := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 1 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 1 by nlinarith), h]
  nlinarith [sq_nonneg (x + y), sq_nonneg (Real.sqrt (x^2 + 1) - Real.sqrt (y^2 + 1)), Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 1 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 1 by nlinarith), sq_nonneg (x - (-y)), sq_nonneg (Real.sqrt (x^2 + 1) + Real.sqrt (y^2 + 1)), Real.sqrt_nonneg (x^2 + 1), Real.sqrt_nonneg (y^2 + 1)]