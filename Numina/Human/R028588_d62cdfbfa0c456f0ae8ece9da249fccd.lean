import Mathlib

theorem algebra_218917 {a b c : ℝ} (h : a^2 + b^2 + c^2 = a * b + b * c + c * a) :
    (a + 2 * b - 3 * c) ^ 2009 = 0 := by
  have h1 : (a - b) ^ 2 ≥ 0 := by apply sq_nonneg
  have h2 : (b - c) ^ 2 ≥ 0 := by apply sq_nonneg
  have h3 : (c - a) ^ 2 ≥ 0 := by apply sq_nonneg
  have h4 : (a - b) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h5 : (b - c) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h6 : (c - a) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hab : a = b := by 
    nlinarith
  have hbc : b = c := by 
    nlinarith
  have hca : c = a := by 
    nlinarith
  have h_zero : a + 2 * b - 3 * c = 0 := by 
    linarith
  rw [h_zero]
  norm_num