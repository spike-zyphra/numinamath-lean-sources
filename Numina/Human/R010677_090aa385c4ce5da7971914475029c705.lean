import Mathlib

/- Find the solution set of the inequality $2x^{2}-x \leqslant 0$. -/
theorem algebra_9190 (x : ℝ) : 2 * x ^ 2 - x ≤ 0 ↔ 0 ≤ x ∧ x ≤ 1 / 2 := by
  -- nlinarith can solve this problem
  constructor <;> intro h
  . constructor <;> nlinarith
  . nlinarith
