import Mathlib

theorem algebra_10272 {a b c d : ℤ} (h₀ : a - b + c = 5) (h₁ : b - c + d = 6) (h₂ : c - d + a = 3) (h₃ : d - a + b = 2) :
    a + b + c + d = 16 := by
  linarith