import Mathlib

/- Solve the system of equations: $\left\{\begin{array}{l}7x-3y=2\\ 2x+y=8\end{array}\right.$. -/
theorem algebra_9399 (x y : ℝ) :
    (7 * x - 3 * y = 2 ∧ 2 * x + y = 8) ↔ (x = 2 ∧ y = 4) := by
  -- Split the problem into two goals
  -- Both goals are solved by linear arithmetic
  constructor <;> intro h <;> constructor <;> linarith
