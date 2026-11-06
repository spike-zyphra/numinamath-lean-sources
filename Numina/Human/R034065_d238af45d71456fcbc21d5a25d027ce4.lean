import Mathlib

/- How many degrees are in the acute angle formed by the hands of a clock at 3:30? -/
theorem algebra_21778 (h : ℝ) (heq : h = 360 / 12) : h / 2 + 2 * h = 75 := by
  linarith