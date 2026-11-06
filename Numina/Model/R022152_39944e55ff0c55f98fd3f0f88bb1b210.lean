import Mathlib

theorem algebra_2278 {b1 b2 g1 g2 : ℕ}
    (h₀ : b1 + g1 + b2 + g2 = 90)
    (h₁ : b1 * 6 = g1 * 5)
    (h₂ : b2 * 11 = g2 * 12) :
    (b1 + b2) * 23 = (g1 + g2) * 22 := by 
  omega