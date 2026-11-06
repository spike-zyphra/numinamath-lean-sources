import Mathlib

theorem algebra_304824 {x y : ℝ} (h : |x - y + 2| = -(x + y - 1)^2) :
    x = -1 / 2 := by
  have h1 : |x - y + 2| ≥ 0 := by apply abs_nonneg
  have h2 : (x + y - 1) ^ 2 ≥ 0 := by apply sq_nonneg
  have h3 : |x - y + 2| + (x + y - 1) ^ 2 = 0 := by 
    linarith
  have h4 : |x - y + 2| = 0 := by linarith [abs_nonneg (x - y + 2), sq_nonneg (x + y - 1)]
  have h5 : (x + y - 1) ^ 2 = 0 := by linarith [abs_nonneg (x - y + 2), sq_nonneg (x + y - 1)]
  have h6 : x - y + 2 = 0 := by 
    rw [abs_eq_zero] at h4
    linarith
  have h7 : x + y - 1 = 0 := by 
    rw [sq_eq_zero_iff] at h5
    linarith
  linarith