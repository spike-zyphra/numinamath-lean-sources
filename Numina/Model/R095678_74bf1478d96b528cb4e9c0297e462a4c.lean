import Mathlib

theorem algebra_223898 {x y z : ℤ} (h : x ≠ y ∧ y ≠ z ∧ x ≠ z) :
    5 * (y - z) * (z - x) * (x - y) ∣ (x - y)^5 + (y - z)^5 + (z - x)^5 := by 
  use (x^2 + y^2 + z^2 - x * y - x * z - y * z)
  ring