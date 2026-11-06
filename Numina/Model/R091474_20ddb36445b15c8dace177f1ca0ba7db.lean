import Mathlib

theorem algebra_226476 (s n : ℝ) (h₀ : 0 < s) (h₁ : 0 < n) (h₂ : 0 < s + n)
    (h₃ : 1 / s + 1 / n = 1 / 20) (h₄ : 1 / s + 1 / (s + n) = 1 / 15)
    (h₅ : 1 / (s + n) + 1 / s = 1 / 12) :
    1 / s = 30 := by
  have h6 : (1 / s + 1 / (s + n)) = (1 / (s + n) + 1 / s) := by
    linarith
  linarith [h₄, h₅, h6]