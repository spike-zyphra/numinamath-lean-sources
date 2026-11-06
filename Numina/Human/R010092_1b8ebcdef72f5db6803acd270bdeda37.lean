import Mathlib

/- Solve the equation: $(x^2-3x+2)(x^2+3x-2)=x^2(x+3)(x-3)$ -/
theorem algebra_9164 (x : ℝ) : (x^2 - 3 * x + 2) * (x^2 + 3 * x - 2) = x^2 * (x + 3) * (x - 3) ↔ x = 1 / 3 := by
  -- The equation can be simplified to: 12x = 4
  -- Thus it is just a linear equation, and linarith tactic can solve it
  constructor <;> intro h <;> linarith
