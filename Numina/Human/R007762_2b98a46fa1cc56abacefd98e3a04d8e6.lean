import Mathlib

/- I take variable $b$, double it, and add four.  I subtract $4b$ from this new expression, and divide the resulting difference by two.  What is my final expression in simplest form? -/
theorem algebra_11291 (b : ℝ) : ((2 * b + 4) - 4 * b) / 2 = 2 - b := by 
  field_simp
  ring