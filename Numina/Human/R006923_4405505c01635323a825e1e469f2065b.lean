import Mathlib

/- Simplify $(a-1)(a+1)(a+2) - (a-2)(a+1).$ -/
theorem algebra_18700 {a : ℝ} : (a - 1) * (a + 1) * (a + 2) - (a - 2) * (a + 1) = a ^ 3 + a ^ 2 := by
  ring