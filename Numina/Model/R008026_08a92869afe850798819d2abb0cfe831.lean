import Mathlib

open Polynomial

theorem algebra_12651 : ((2 * X ^ 2 + 3 * X + 7) * (X + 1) - (X + 1) * (X ^ 2 + 4 * X - 63) +
    (3 * X - 14) * (X + 1) * (X + 5) : ℤ[X]) = 4 * X ^ 3 + 4 * X ^ 2 := by
  ring