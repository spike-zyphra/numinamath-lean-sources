import Mathlib

/- The number $x$ satisfies $5x^2 + 4 = 3x + 9$.  Find the value of $(10x - 3)^2$. -/
theorem algebra_14205 {x : ℝ} (h : 5 * x ^ 2 + 4 = 3 * x + 9) : (10 * x - 3) ^ 2 = 109 := by
  nlinarith [h]