import Mathlib

theorem algebra_6052 (x y : ℝ) (h : x^2 + y^2 + 58 = 14 * x - 6 * y) : x * y = -21 := by
  have h1 : (x - 7) ^ 2 + (y + 3) ^ 2 = 0 := by
    nlinarith
  have h2 : (x - 7) ^ 2 = 0 := by 
    linarith [sq_nonneg (x - 7), sq_nonneg (y + 3)]
  have h3 : (y + 3) ^ 2 = 0 := by 
    linarith [sq_nonneg (x - 7), sq_nonneg (y + 3)]
  have h4 : x - 7 = 0 := by 
    rwa [sq_eq_zero_iff] at h2
  have h5 : y + 3 = 0 := by 
    rwa [sq_eq_zero_iff] at h3
  have hx : x = 7 := by 
    linarith
  have hy : y = -3 := by 
    linarith
  rw [hx, hy]
  norm_num