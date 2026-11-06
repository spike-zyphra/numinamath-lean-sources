import Mathlib

theorem algebra_3452 (p q r : ℝ) : (p ^ 2 + 2 * p * q + q ^ 2 - r ^ 2 + 2 * r - 1) =
    (p + q - r + 1) * (p + q + r - 1) := by
  ring