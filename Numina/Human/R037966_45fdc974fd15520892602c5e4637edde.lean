import Mathlib

theorem algebra_195789 (x y z : ℝ) :
    (x^2 + y^2) * (y^2 + z^2) = (x * y + y * z)^2 ↔ y ^ 2 = x * z := by
  have H (x y z : ℝ) : (x^2 + y^2) * (y^2 + z^2) - (x * y + y * z)^2 = (y ^ 2 - x * z) ^ 2 := by ring
  rw [← sub_eq_zero, H]
  simp [sub_eq_zero]
