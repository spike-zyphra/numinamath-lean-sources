import Mathlib

/- The range of $x$ for the quadratic function $y = x^2 - 4x + 3$ when $y < 0$ is __________. -/
theorem algebra_9106 (x : ℝ) : x ^ 2 - 4 * x + 3 < 0 ↔ 1 < x ∧ x < 3 := by
  -- nlinarith can solve this problem
  constructor <;> intro h
  . constructor <;> nlinarith
  . nlinarith
