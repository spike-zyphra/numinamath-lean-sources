import Mathlib

theorem algebra_183814 (x y z : ℝ) (h₀ : x + y + z = 12000) (h₁ : x / 2 = y + z)
    (h₂ : y / 2 = x + z) (h₃ : z / 2 = x + y) :
    x = 2000 ∧ y = 3500 ∧ z = 6500 := by
  linarith