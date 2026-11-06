import Mathlib

theorem algebra_188904 (x y z : ℤ) (h : x ≠ y ∧ y ≠ z ∧ z ≠ x) :
    5 * (x - y) * (y - z) * (z - x) ∣ (x - y) ^ 5 + (y - z) ^ 5 + (z - x) ^ 5 := by 
  rcases h with ⟨hxy, hyz, hzx⟩
  use (x^2 + y^2 + z^2 - x * y - y * z - z * x)
  ring