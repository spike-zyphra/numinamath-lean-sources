import Mathlib

/- If $x$ is a positive number, by how much does $x+10$ exceed $10-x$? Express your answer in terms of $x$. -/
theorem algebra_21355 (x : ℝ) (hx : x > 0) : (x + 10 - (10 - x)) = 2 * x := by 
  ring_nf