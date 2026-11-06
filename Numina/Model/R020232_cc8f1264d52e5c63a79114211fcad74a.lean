import Mathlib

theorem algebra_3355 (x y : ℝ) (h : x ^ 2 + y ^ 2 + 10 * x + 12 * y + 2019 = 1958) :
    x ^ 2 + y ^ 2 = 61 := by
  have h1 : x^2 + y^2 + 10 * x + 12 * y + 61 = 0 := by
    nlinarith
  have h2 : (x + 5) ^ 2 + (y + 6) ^ 2 = 0 := by
    nlinarith [h1]
  have hx1 : (x + 5) ^ 2 = 0 := by
    linarith [sq_nonneg (x + 5), sq_nonneg (y + 6)]
  have hy1 : (y + 6) ^ 2 = 0 := by
    linarith [sq_nonneg (x + 5), sq_nonneg (y + 6)]
  have hx2 : x + 5 = 0 := by
    rwa [sq_eq_zero_iff] at hx1
  have hy2 : y + 6 = 0 := by
    rwa [sq_eq_zero_iff] at hy1
  have hx3 : x = -5 := by
    linarith
  have hy3 : y = -6 := by
    linarith
  rw [hx3, hy3]
  norm_num