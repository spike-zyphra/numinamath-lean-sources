import Mathlib

theorem algebra_20593 {a b c d e f : ℝ}
    (h₀ : a + b + c + d + e + f = 0)
    (h₁ : a + 2 * b + 3 * c + 4 * d + 2 * e + 2 * f = 0)
    (h₂ : a + 3 * b + 6 * c + 9 * d + 4 * e + 6 * f = 0)
    (h₃ : a + 4 * b + 10 * c + 16 * d + 8 * e + 24 * f = 0)
    (h₄ : a + 5 * b + 15 * c + 25 * d + 16 * e + 120 * f = 42) :
    a + 6 * b + 21 * c + 36 * d + 32 * e + 720 * f = 508 := by 
  linarith