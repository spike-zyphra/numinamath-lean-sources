import Mathlib

theorem algebra_5961 {x y : ℝ} (h : x ^ 2 + 8 * y = 12 * x - y ^ 2 - 52) : x * y = -24 := by
  have h1 : x ^ 2 - 12 * x + y ^ 2 + 8 * y + 52 = 0 := by 
    nlinarith
  
  have h2 : (x - 6) ^ 2 + (y + 4) ^ 2 = 0 := by
    nlinarith

  have h3 : (x - 6) ^ 2 = 0 := by 
    linarith [sq_nonneg (x - 6), sq_nonneg (y + 4)]

  have h4 : (y + 4) ^ 2 = 0 := by 
    linarith [sq_nonneg (x - 6), sq_nonneg (y + 4)]

  have hx : x - 6 = 0 := by 
    rwa [sq_eq_zero_iff] at h3

  have hy : y + 4 = 0 := by 
    rwa [sq_eq_zero_iff] at h4

  have hx2 : x = 6 := by linarith

  have hy2 : y = -4 := by linarith

  rw [hx2, hy2]
  norm_num