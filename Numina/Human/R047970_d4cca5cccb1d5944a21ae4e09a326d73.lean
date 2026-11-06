import Mathlib

/- Expand $(2x^5 + 3x^2)(x^4 - 4x^2 + 3x - 8)$. -/
theorem algebra_18865 (x : ℝ) :
    (2 * x ^ 5 + 3 * x ^ 2) * (x ^ 4 - 4 * x ^ 2 + 3 * x - 8) =
    2 * x ^ 9 - 8 * x ^ 7 + 9 * x ^ 6 - 16 * x ^ 5 - 12 * x ^ 4 + 9 * x ^ 3 - 24 * x ^ 2 := by 
  ring