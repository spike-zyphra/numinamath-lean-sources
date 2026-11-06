import Mathlib

theorem algebra_279470 (a b c d e f g : ℕ)
    (h₀ : (a + b + c) / 3 = 12 * 12 + 3)
    (h₁ : (d + e + f + g) / 4 = 13 * 12 + 5) :
    (a + b + c + d + e + f + g) / 7 = 155 := by
  omega