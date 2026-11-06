import Mathlib

theorem algebra_203712 {p q : ℤ} :
    (1^2 + (p * q + 2)^2 + (p * q + p - 2 * q)^2 + (2 * p * q + p - 2 * q + 1)^2) =
    (2^2 + (p * q + p + 1)^2 + (p * q - 2 * q + 1)^2 + (2 * p * q + p - 2 * q)^2) := by
  ring