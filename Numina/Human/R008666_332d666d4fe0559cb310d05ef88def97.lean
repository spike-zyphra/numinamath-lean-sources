import Mathlib

/- Solve the inequality $x^2 - x - 6 < 0$.-/
theorem algebra_9133 (x : ℝ) : x^2 - x - 6 < 0 ↔ -2 < x ∧ x < 3 := by
  -- According to the problem,
  -- The original inequality can be transformed into $(x-3)(x+2) < 0$.
  -- Solving this, we get $-2 < x < 3$.
  -- Therefore, the solution to the inequality is $\boxed{-2 < x < 3}$.
  constructor <;> intro h
  . constructor <;> nlinarith
  nlinarith
