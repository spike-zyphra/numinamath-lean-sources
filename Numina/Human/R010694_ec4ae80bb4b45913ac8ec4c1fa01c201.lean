import Mathlib

/- Solve the inequality $(x-2)(x+2) < 5$. -/
theorem algebra_9249 (x : ℝ) : (x - 2) * (x + 2) < 5 ↔ -3 < x ∧ x < 3 := by
  -- Split the goal into two
  constructor <;> intro h
  . -- Prove -3 < x and x < 3 respectively
    -- Both goals can be solved by nlinarith tactic
    constructor <;> nlinarith
  . -- Nlinarith tactic can solve the goal
    nlinarith
