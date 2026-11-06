import Mathlib

/- Expand $(z^2 -3z+2)(z^3 + 4z-2).$ -/
theorem algebra_21312 (Z : ℝ) : (Z ^ 2 - 3 * Z + 2) * (Z ^ 3 + 4 * Z - 2) =
    Z ^ 5 - 3 * Z ^ 4 + 6 * Z ^ 3 - 14 * Z ^ 2 + 14 * Z - 4 := by
        ring_nf
