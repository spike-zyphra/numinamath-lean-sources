import Mathlib

theorem algebra_5391 {a b : ℝ} (h : (2*a+3)^2+(b-2)^2=0) (x : ℝ) (h' : a*x+4*b=5) :
    x=2 := by 
  have h1 : (2 * a + 3) ^ 2 = 0 := by
    linarith [sq_nonneg (2 * a + 3), sq_nonneg (b - 2)]
  have h2 : (b - 2) ^ 2 = 0 := by
    linarith [sq_nonneg (2 * a + 3), sq_nonneg (b - 2)]
  have ha : a = -3 / 2 := by
    nlinarith
  have hb : b = 2 := by
    nlinarith
  rw [ha, hb] at h'
  linarith