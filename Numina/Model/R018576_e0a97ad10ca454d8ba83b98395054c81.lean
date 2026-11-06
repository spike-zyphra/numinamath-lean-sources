import Mathlib

theorem algebra_102110 (x y : ℝ) (h : 5 * x ^ 2 + y ^ 2 - 4 * x * y + 24 ≤ 10 * x - 1) :
    x ^ 2 + y ^ 2 = 125 := by

  have h1 : (x - 5) ^ 2 + (y - 2 * x) ^ 2 ≤ 0 := by 
    nlinarith
  have h2 : (x - 5) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 2 * x)]
  have h3 : x = 5 := by 
    nlinarith
  have h4 : (y - 2 * x) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 2 * x)]
  have h5 : y - 2 * x = 0 := by 
    nlinarith [h4]
  have h6 : y = 10 := by
    rw [show x = 5 by linarith] at h5
    linarith
  rw [h3, h6]
  norm_num