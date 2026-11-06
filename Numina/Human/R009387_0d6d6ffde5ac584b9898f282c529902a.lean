import Mathlib

/- Simplify the following: $(2y-1)\cdot(4y^{10}+2y^9+4y^8+2y^7).$  Express your answer as a polynomial with the degrees of the terms in decreasing order. -/
theorem algebra_13425 (y : ℝ) :
    (2 * y - 1) * (4 * y ^ 10 + 2 * y ^ 9 + 4 * y ^ 8 + 2 * y ^ 7) =
    8 * y ^ 11 + 6 * y ^ 9 - 2 * y ^ 7 := by
  ring