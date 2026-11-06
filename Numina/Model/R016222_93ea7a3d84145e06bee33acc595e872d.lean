import Mathlib

theorem algebra_126366 (a b c d e : ℝ) (h₀ : a + b + c + d + e = 8) (h₁ : a^2 + b^2 + c^2 + d^2 + e^2 = 16) :
    max (max (max (max a b) c) d) e ≤ 16 / 5 := by
  have h2 : a ≤ 16 / 5 := by 
    nlinarith [sq_nonneg (a - 16 / 5), sq_nonneg (b - 6 / 5), sq_nonneg (c - 6 / 5), sq_nonneg (d - 6 / 5), sq_nonneg (e - 6 / 5)]
  have h3 : b ≤ 16 / 5 := by 
    nlinarith [sq_nonneg (b - 16 / 5), sq_nonneg (a - 6 / 5), sq_nonneg (c - 6 / 5), sq_nonneg (d - 6 / 5), sq_nonneg (e - 6 / 5)]
  have h4 : c ≤ 16 / 5 := by 
    nlinarith [sq_nonneg (c - 16 / 5), sq_nonneg (a - 6 / 5), sq_nonneg (b - 6 / 5), sq_nonneg (d - 6 / 5), sq_nonneg (e - 6 / 5)]
  have h5 : d ≤ 16 / 5 := by 
    nlinarith [sq_nonneg (d - 16 / 5), sq_nonneg (a - 6 / 5), sq_nonneg (b - 6 / 5), sq_nonneg (c - 6 / 5), sq_nonneg (e - 6 / 5)]
  have h6 : e ≤ 16 / 5 := by 
    nlinarith [sq_nonneg (e - 16 / 5), sq_nonneg (a - 6 / 5), sq_nonneg (b - 6 / 5), sq_nonneg (c - 6 / 5), sq_nonneg (d - 6 / 5)]
  have h7 : max (max (max (max a b) c) d) e ≤ 16 / 5 := by
    simp [max_le_iff, h2, h3, h4, h5, h6]
  linarith