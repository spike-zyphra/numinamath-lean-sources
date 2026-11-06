import Mathlib

open Polynomial

/- Factor $(x^2 + 3x + 2)(x^2 + 7x + 12) + (x^2 + 5x - 6)$ as the product of two non-constant polynomials. -/
theorem algebra_11173 {P Q R : Polynomial ℝ} (hP : P = X ^ 2 + 3 * X + 2)
    (hQ : Q = X ^ 2 + 7 * X + 12) (hR : R = X ^ 2 + 5 * X - 6) :
    (P * Q + R) = (X ^ 2 + 5 * X + 2) * (X ^ 2 + 5 * X + 9) := by
  rw [hP, hQ, hR]
  ring