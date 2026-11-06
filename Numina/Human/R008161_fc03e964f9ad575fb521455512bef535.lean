import Mathlib

theorem algebra_178093 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a / b = (2 + 3 / 4) / (1 + 5 / 6))
    (h₄ : b / c = (1 + 5 / 6) / (1 + 3 / 8))
    (h₅ : a * 18 = b * 18 + 72) :
    a + b + c = 26 := by
  field_simp at *
  linarith
