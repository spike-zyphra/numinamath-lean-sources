import Mathlib

theorem algebra_107523 (x y z : ℤ) (h₀ : x ≠ y) (h₁ : y ≠ z) (h₂ : z ≠ x) :
    5 * (y - z) * (z - x) * (x - y) ∣ (x - y)^5 + (y - z)^5 + (z - x)^5 := by

  use (x^2 + y^2 + z^2 - x * y - x * z - y * z)
  ring