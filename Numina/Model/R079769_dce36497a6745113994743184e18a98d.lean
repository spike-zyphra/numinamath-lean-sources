import Mathlib

theorem algebra_158310 {x y z : ℝ} (h₀ : x * y + y * z + z * x = x * y * z) (h₁ : x + y + z = 1) :
    x^3 + y^3 + z^3 = 1 := by
  have h2 : x^3 + y^3 + z^3 = (x + y + z) ^ 3 - 3 * (x + y + z) * (x * y + y * z + z * x) + 3 * (x * y * z) := by
    ring
  rw [h2, h₁, h₀]
  ring