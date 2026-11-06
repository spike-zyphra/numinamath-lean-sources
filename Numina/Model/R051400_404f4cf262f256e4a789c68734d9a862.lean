import Mathlib

theorem algebra_4930 {a b : ℝ} (h : (a - 5) ^ 2 + (b + 2) ^ 2 = 0) (x : ℝ) (h' : -2 * b * x + 3 * a = 11) :
    x = -1 := by
  have h1 : (a - 5) ^ 2 = 0 := by
    linarith [sq_nonneg (a - 5), sq_nonneg (b + 2)]
  have ha : a = 5 := by
    nlinarith
  have h2 : (b + 2) ^ 2 = 0 := by
    linarith [sq_nonneg (a - 5), sq_nonneg (b + 2)]
  have hb : b = -2 := by
    nlinarith
  rw [hb] at h'
  rw [ha] at h'
  linarith