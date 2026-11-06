import Mathlib

theorem algebra_597254 (x y z : ℤ) (h : x ≠ y ∧ y ≠ z ∧ x ≠ z) :
    5 * (y - z) * (z - x) * (x - y) ∣ (x - y)^5 + (y - z)^5 + (z - x)^5 := by

  have h1 : (x - y)^5 + (y - z)^5 + (z - x)^5 = 5 * (x - y) * (y - z) * (z - x) * (x^2 + y^2 + z^2 - x * y - y * z - z * x) := by
    ring_nf
  
  rw [h1]
  
  use (x^2 + y^2 + z^2 - x * y - y * z - z * x)
  
  all_goals ring