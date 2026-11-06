import Mathlib

theorem algebra_168394 (x y z : ℤ) (h : x ≠ y ∧ y ≠ z ∧ z ≠ x) :
    5 * (y - z) * (z - x) * (x - y) ∣ (x - y)^5 + (y - z)^5 + (z - x)^5 := by
  have eq1 : (x - y)^5 + (y - z)^5 + (z - x)^5 =
      5 * (y - z) * (z - x) * (x - y) * (x^2 + y^2 + z^2 - x * y - y * z - z * x) := by
    ring
  rw [eq1]
  -- once written as $5 * (y - z) * (z - x) * (x - y)$ multiplied by some polynomial, the divisibility follows.
  use x^2 + y^2 + z^2 - x * y - y * z - z * x
  all_goals ring