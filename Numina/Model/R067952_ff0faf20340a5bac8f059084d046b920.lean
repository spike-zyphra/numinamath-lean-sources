import Mathlib

theorem algebra_254233 (a b c d e : ℝ) (h₀ : a < b) (h₁ : b < c) (h₂ : c < d)
    (h₃ : d < e) (h₄ : a * b = 3) (h₅ : a * c = 6) (h₆ : a * d = 15) (h₇ : a * e = 18)
    (h₈ : b * c = 20) (h₉ : b * d = 50) (h₁₀ : b * e = 60) (h₁₁ : c * d = 100) (h₁₂ : c * e = 120)
    (h₁₃ : d * e = 300) :
    b ^ 2 = 10 := by
  have h14 : c = 2 * b := by
    nlinarith
  rw [h14] at h₈
  nlinarith