import Mathlib

/- Simplify $(5x+3) - 2(2x-4)$. -/
theorem algebra_19761 (x : ℝ) : (5 * x + 3) - 2 * (2 * x - 4) = 11 + x := by
  -- 化简代数表达式
  ring_nf
  -- 化简后得到 11 + x
