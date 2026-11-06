import Mathlib

theorem algebra_283705 (a b c d e f : ℝ) :
    ∃ x y z, (a^3 + b^3 + c^3 - 3 * a * b * c) * (d^3 + e^3 + f^3 - 3 * d * e * f) =
    x^3 + y^3 + z^3 - 3 * x * y * z := by
  use a * d + b * e + c * f, a * e + b * f + c * d, a * f + b * d + c * e
  ring_nf