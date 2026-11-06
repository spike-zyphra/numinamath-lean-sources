import Mathlib

theorem algebra_218917 {a b c : ℝ} (h : a^2 + b^2 + c^2 = a * b + b * c + c * a) :
    (a + 2 * b - 3 * c) ^ 2009 = 0 := by
  have h1 : (a - b)^2 + (b - c)^2 + (c - a)^2 = 0 := by
    nlinarith
  have h2 : a - b = 0 := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h3 : b - c = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h4 : c - a = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h8 : a + 2 * b - 3 * c = 0 := by
    have h5 : a = b := by linarith
    have h6 : b = c := by linarith
    have h7 : a = c := by linarith
    nlinarith [h5, h6, h7]
  rw [h8]
  norm_num