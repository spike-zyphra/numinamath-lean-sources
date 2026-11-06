import Mathlib

/- Expand $(2z^2 + 5z - 6)(3z^3 - 2z + 1)$. -/
theorem algebra_15685 (z : ℝ) : (2 * z ^ 2 + 5 * z - 6) * (3 * z ^ 3 - 2 * z + 1) =
    6 * z ^ 5 + 15 * z ^ 4 - 22 * z ^ 3 - 8 * z ^ 2 + 17 * z - 6 := by 
  ring