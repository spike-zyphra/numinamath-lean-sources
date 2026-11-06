import Mathlib

theorem algebra_21168 (a b c d : ℕ) (h₀ : a + b + c + d = 27) (h₁ : a = b - 5) (h₂ : b = c + 4)
    (h₃ : d = 3 * b) : d = 18 := by
  omega