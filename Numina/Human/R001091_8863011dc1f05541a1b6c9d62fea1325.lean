import Mathlib

/- Suppose $x$ is a solution to $x^2 + 1 = 7x$. What is the sum of $x$ and its reciprocal? -/
theorem algebra_20408 {x : ℝ} (hx : x^2 + 1 = 7 * x) : x + 1 / x = 7 := by 
  have h : x ≠ 0 := by nlinarith
  field_simp at *
  nlinarith