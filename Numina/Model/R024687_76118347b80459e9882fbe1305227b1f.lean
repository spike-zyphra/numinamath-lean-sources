import Mathlib

theorem inequalities_598222 (k a b c : ℝ) (h₀ : 0 < c) (h₁ : c < b) (h₂ : b < a)
    (h₃ : a < k) :
    k^2 - (a + b + c)*k + (a*b + b*c + c*a) > 0 := by 
  have h4 : a > 0 := by linarith
  have h5 : 0 < b := by linarith
  have h6 : k > a := by linarith
  have h7 : k > 0 := by linarith
  nlinarith [sq_nonneg (k - (a + b + c) / 2), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), sq_nonneg (k - a), sq_nonneg (k - b), sq_nonneg (k - c), sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (a * c), sq_nonneg ((a + b + c) / 2 - a), sq_nonneg ((a + b + c) / 2 - b), sq_nonneg ((a + b + c) / 2 - c), mul_pos (sub_pos.mpr h₀) (sub_pos.mpr h₁), mul_pos (sub_pos.mpr h₀) (sub_pos.mpr h₂), mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂), mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₂), mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₁), mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₀)]