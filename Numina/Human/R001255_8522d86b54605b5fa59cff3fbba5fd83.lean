import Mathlib

/- If $x^2 - x - 1 = 0$, what is the value of $x^3 - 2x + 1$? -/
theorem algebra_22142 {x : ℝ} (hx : x^2 - x - 1 = 0) : x^3 - 2 * x + 1 = 2 := by 
  nlinarith [sq_nonneg (x^2 - 1)]