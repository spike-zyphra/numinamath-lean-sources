import Mathlib

theorem inequalities_316554 (a b c d e : ℝ) (h₀ : 0 ≤ a) (h₁ : a ≤ b) (h₂ : b ≤ c)
    (h₃ : c ≤ d) (h₄ : d ≤ e) (h₅ : a + b + c + d + e = 1) :
    a * d + c * d + c * b + b * e + e * a ≤ 1 / 5 := by
  nlinarith [sq_nonneg (a - 1 / 5), sq_nonneg (b - 1 / 5), sq_nonneg (c - 1 / 5), sq_nonneg (d - 1 / 5), sq_nonneg (e - 1 / 5), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - e),
          h₀, h₁, h₂, h₃, h₄, h₅]