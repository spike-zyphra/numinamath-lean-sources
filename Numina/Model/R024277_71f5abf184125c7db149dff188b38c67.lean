import Mathlib

theorem algebra_78736 {x y : ℝ} (h : (x ^ 2 + 1) * (y ^ 2 + 1) + 9 = 6 * (x + y)) :
    x ^ 2 + y ^ 2 = 7 := by
  have h1 : (x * y) ^ 2 + x ^ 2 + y ^ 2 + 10 = 6 * (x + y) := by
    nlinarith
  have h2 : (x * y - 1) ^ 2 + (x + y - 3) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 3), sq_nonneg (x * y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1)]
  have h3 : x * y - 1 = 0 := by
    nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x + y - 3)]
  have h4 : x * y = 1 := by linarith
  have h5 : x + y - 3 = 0 := by 
    nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x + y - 3)]
  have h6 : x + y = 3 := by linarith
  have h7 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
    linarith
  rw [show x + y = 3 by linarith] at h7
  rw [show x * y = 1 by linarith] at h7
  linarith