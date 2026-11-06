import Mathlib

theorem inequalities_200103 (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b ≤ c) (h₂ : c ≤ d)
    (h₃ : d ≤ e) (h₄ : a + b + c + d + e = 1) :
    a * d + d * c + c * b + b * e + e * a ≤ 1 / 5 := by 
  nlinarith [sq_nonneg (a - 1 / 5), sq_nonneg (b - 1 / 5), sq_nonneg (c - 1 / 5), sq_nonneg (d - 1 / 5), sq_nonneg (e - 1 / 5),
    h₀, h₁, h₂, h₃, h₄]