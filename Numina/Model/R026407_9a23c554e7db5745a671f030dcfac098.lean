import Mathlib

theorem number_theory_36332 (x y z : ℤ) (h : x ≠ y ∧ y ≠ z ∧ x ≠ z) :
    5 * (x - y) * (y - z) * (z - x) ∣ (x - y)^5 + (y - z)^5 + (z - x)^5 := by
  use x^2 + y^2 + z^2 - x * y - y * z - z * x
  ring