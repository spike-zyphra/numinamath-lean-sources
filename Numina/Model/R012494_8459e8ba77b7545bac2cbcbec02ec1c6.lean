import Mathlib

theorem algebra_16959 (v w x y z : ℤ) (h₀ : v + w + x = 25 + z + 21) (h₁ : w + x + y = 18 + z + 24)
    (h₂ : x + y + z = 25 + 18 + 21) (h₃ : y + z + v = 25 + 18 + 21) (h₄ : z + v + w = 25 + 18 + 21) :
    y + z = 46 := by
  omega