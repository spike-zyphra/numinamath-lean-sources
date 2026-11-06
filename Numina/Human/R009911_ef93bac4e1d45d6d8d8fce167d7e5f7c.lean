import Mathlib

/- If $a < b$, what is the value of $|a-b|+a+b$? -/
theorem algebra_20065 {a b : ℝ} (h : a < b) : |a - b| + a + b = 2 * b := by
  have le : a - b < 0 := by
    linarith
  rw [abs_of_neg le]
  ring