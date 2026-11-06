import Mathlib

theorem inequalities_115819 (a b c d e : ℝ)
    (h₀ : 0 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) (h₁ : a + b + c + d + e = 1) :
    a * d + d * c + c * b + b * e + e * a ≤ 1 / 5 := by
  rcases h₀ with ⟨h₀0, h₀1, h₀2, h₀3, h₀4⟩
  have h2 : a + b + c + d + e = 1 := h₁
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - e),
          sq_nonneg (a - 1 / 5), sq_nonneg (b - 1 / 5), sq_nonneg (c - 1 / 5), sq_nonneg (d - 1 / 5), sq_nonneg (e - 1 / 5),
          h₀0, h₀1, h₀2, h₀3, h₀4]