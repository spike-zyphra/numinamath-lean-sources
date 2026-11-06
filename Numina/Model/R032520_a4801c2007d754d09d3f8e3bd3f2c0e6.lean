import Mathlib

theorem algebra_282219 (x y z : ℝ) :
    (x^2 + y^2) * (x + y + z) * (x + y - z) =
    (x^2 + x * y + y^2)^2 - (x^2 * y^2 + y^2 * z^2 + z^2 * x^2) := by
  ring