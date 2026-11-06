import Mathlib

theorem algebra_284500 (x y z w : ℤ) (h₀ : x + 4 = y) (h₁ : y / 4 = z) (h₂ : z - 4 = w)
    (h₃ : w * 4 = x) (h₄ : x + 4 + z + w = 80) :
    x = 38 ∧ y = 26 ∧ z = 14 ∧ w = 2 := by
  omega