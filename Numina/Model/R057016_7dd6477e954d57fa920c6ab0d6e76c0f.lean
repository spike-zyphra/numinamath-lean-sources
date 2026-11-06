import Mathlib

theorem algebra_4159 (a b c d : ℤ) (h₀ : a = 4 * b) (h₁ : c = 5 * b) (h₂ : 3 * d = b)
    (h₃ : a + b + c + d = 341) : c = 165 := by
  omega