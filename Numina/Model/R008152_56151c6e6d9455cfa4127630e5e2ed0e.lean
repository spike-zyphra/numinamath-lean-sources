import Mathlib

theorem algebra_14535 {x y : ℝ} (h : x^2 + y^2 = 10 * x - 6 * y - 34) : x + y = 2 := by
  have h1 : (x - 5) ^ 2 + (y + 3) ^ 2 = 0 := by 
    nlinarith
  have hx1 : (x - 5) ^ 2 = 0 := by
    linarith [sq_nonneg (x - 5), sq_nonneg (y + 3)]
  have hy1 : (y + 3) ^ 2 = 0 := by
    linarith [sq_nonneg (x - 5), sq_nonneg (y + 3)]
  have hx2 : x - 5 = 0 := by
    rwa [sq_eq_zero_iff] at hx1
  have hy2 : y + 3 = 0 := by
    rwa [sq_eq_zero_iff] at hy1
  have hx3 : x = 5 := by linarith
  have hy3 : y = -3 := by linarith
  linarith [hx3, hy3]