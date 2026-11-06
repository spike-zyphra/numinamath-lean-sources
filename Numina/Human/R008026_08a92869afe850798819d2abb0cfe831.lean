import Mathlib

open Polynomial

/- Write the following expression as a polynomial: $$(2x^2+3x+7)(x+1)-(x+1)(x^2+4x-63)+(3x-14)(x+1)(x+5).$$ -/
theorem algebra_12651 : ((2 * X ^ 2 + 3 * X + 7) * (X + 1) - (X + 1) * (X ^ 2 + 4 * X - 63) +
    (3 * X - 14) * (X + 1) * (X + 5) : ℤ[X]) = 4 * X ^ 3 + 4 * X ^ 2 := by ring
