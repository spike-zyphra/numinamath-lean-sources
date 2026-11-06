import Mathlib

open Polynomial

theorem algebra_12985 (P : Polynomial ℤ) (hP : P = X^10 + X^5 + 1) : P = (X^2 + X + 1) * (X^8 - X^7 + X^5 - X^4 + X^3 - X + 1) := by
  rw [hP]
  ring -- Expands and simplifies the polynomial multiplication