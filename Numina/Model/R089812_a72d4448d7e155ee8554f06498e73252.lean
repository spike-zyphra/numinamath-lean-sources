import Mathlib

theorem algebra_98007 (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b ≤ c) (h₂ : c ≤ d)
    (h₃ : d ≤ e) (h₄ : (a + b + c + d + e) / 5 = 10) (h₅ : c = 12) :
    e - a ≥ 5 := by

  have h6 : a + b + c + d + e = 50 := by
    linarith

  rw [h₅] at h6

  linarith