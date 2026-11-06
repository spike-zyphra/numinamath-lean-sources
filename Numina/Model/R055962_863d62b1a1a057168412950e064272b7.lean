import Mathlib

theorem algebra_318283 : ∀ x y z : ℝ, x * y * z * (x^3 + y^3 + z^3) - x^3 * y^3 - y^3 * z^3 - z^3 * x^3 =
    (x^2 - y * z) * (y^2 - z * x) * (z^2 - x * y) := by
  intro x y z
  ring