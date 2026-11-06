import Mathlib

/- Real numbers $x$ and $y$ satisfy the equation $x^2 + y^2 = 10x - 6y - 34$.  What is $x+y$? -/
theorem algebra_14535 {x y : ℝ} (h : x^2 + y^2 = 10 * x - 6 * y - 34) : x + y = 2 := by
  have : (x - 5) ^ 2 + (y + 3) ^ 2 = 0 := by linarith
  have : x = 5 := by nlinarith
  have : y = -3 := by nlinarith
  linarith
