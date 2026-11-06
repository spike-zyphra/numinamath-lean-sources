import Mathlib

theorem algebra_5821 {a b : ℝ} (h : (a - 3)^2 + (b + 1)^2 = 0) (x : ℝ) (hx : a * x + b = 5) :
    x = 2 := by
  have ha1 : (a - 3) ^ 2 = 0 := by
    linarith [sq_nonneg (a - 3), sq_nonneg (b + 1)]
  have ha2 : a - 3 = 0 := by
    rwa [sq_eq_zero_iff] at ha1
  have ha3 : a = 3 := by 
    linarith
  have hb1 : (b + 1) ^ 2 = 0 := by
    linarith [sq_nonneg (a - 3), sq_nonneg (b + 1)]
  have hb2 : b + 1 = 0 := by
    rwa [sq_eq_zero_iff] at hb1
  have hb3 : b = -1 := by
    linarith
  rw [ha3, hb3] at hx
  linarith