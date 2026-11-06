import Mathlib

theorem algebra_15954 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 + c^2 = 1800) (h₄ : c^2 = a^2 + b^2) :
    c = 30 := by
  have h₆ : 2 * c^2 = 1800 := by
    nlinarith [h₃, h₄]
  have h₇ : c^2 = 900 := by
    nlinarith
  have h₈ : c = 30 := by
    nlinarith [h₇, h₂]
  exact h₈