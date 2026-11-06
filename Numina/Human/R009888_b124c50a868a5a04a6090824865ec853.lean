import Mathlib

/- Simplify $((5p+1)-2p\cdot4)(3)+(4-1\div3)(6p-9)$ to a much simpler expression of the form $ap-b$ , where $a$ and $b$ are positive integers. -/
theorem algebra_11150 {p : ℝ} : ((5 * p + 1) - 2 * p * 4) * 3 + (4 - 1 / 3) * (6 * p - 9) = 13 * p - 30 := by
  linarith