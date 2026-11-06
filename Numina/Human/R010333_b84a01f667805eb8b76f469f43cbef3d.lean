import Mathlib

/- Solve the inequality system: $\left\{\begin{array}{l}{x>-6-2x}\\{x\leq\frac{3+x}{4}}\end{array}\right.$.-/
theorem algebra_9224 (x : ℝ) :
    (x > -6 - 2 * x ∧ x ≤ (3 + x) / 4) ↔ (-2 < x ∧ x ≤ 1) := by
  -- 1. For the first inequality $x > -6 - 2x$:
  --  - We start by adding $2x$ to both sides of the inequality to get $x + 2x > -6$.
  --  - Simplifying this, we get $3x > -6$.
  --  - Dividing both sides by $3$, we find $x > -2$.
  have hx1 : x > -6 - 2 * x ↔ -2 < x := by
    constructor <;> intro h <;> linarith
  -- 2. For the second inequality $x \leq \frac{3 + x}{4}$:
  --  - Multiplying both sides by $4$ to clear the denominator, we get $4x \leq 3 + x$.
  --  - Subtracting $x$ from both sides gives $3x \leq 3$.
  --  - Dividing both sides by $3$, we find $x \leq 1$.
  have hx2 : x ≤ (3 + x) / 4 ↔ x ≤ 1 := by
    constructor <;> intro h <;> linarith
  -- Combining the results from both inequalities, we determine that the solution set for the system is $-2 < x \leq 1$.
  rw [hx1, hx2]
