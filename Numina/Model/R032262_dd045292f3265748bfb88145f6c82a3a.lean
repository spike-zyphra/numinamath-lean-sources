import Mathlib

theorem algebra_312645 (x y : ℝ) (h : x * y - x - y = 1) :
    x ^ 2 + y ^ 2 ≥ 6 - 4 * Real.sqrt 2 := by 
  have h1 : x * y = x + y + 1 := by linarith 
  have h2 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by 
    nlinarith 
  rw [h2, h1] 
  have h5 : (x + y) ^ 2 - 4 * (x + y + 1) ≥ 0 := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x * y), sq_nonneg (x + y - 2)]
  have h6 : ((x + y) - (2 + 2 * Real.sqrt 2)) * ((x + y) - (2 - 2 * Real.sqrt 2)) ≥ 0 := by 
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (x + y - 2), sq_nonneg (Real.sqrt 2), Real.sqrt_nonneg 2, h5]
  nlinarith [sq_nonneg ((x + y) - (2 - 2 * Real.sqrt 2)), sq_nonneg (x - y), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg ((x + y) - 2), sq_nonneg (x - y), Real.sqrt_nonneg 2]