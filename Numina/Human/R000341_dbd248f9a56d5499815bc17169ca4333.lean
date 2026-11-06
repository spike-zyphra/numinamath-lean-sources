import Mathlib

/-Solve the inequality $x + |2x + 3| \geqslant 2$.-/
theorem algebra_9004 (x : ℝ) :
  x + abs (2 * x + 3) ≥ 2 ↔ x ≤ -5 ∨ x ≥ -1 / 3 := by
    by_cases h : 2 * x + 3 ≥ 0
    --Case 1: If $2x+3 \geq 0$, which means $x \geq -\frac{3}{2}$, the inequality simplifies to:
    --\[ x + (2x + 3) \geqslant 2 \]
    rw [abs_eq_self.2 h]
    constructor
    intro leq
    have : 3 * x + 3 ≥ 2 := by linarith
    --\[ 3x + 3 \geqslant 2 \]
    have : 3 * x ≥ -1 := by linarith
    --\[ 3x \geqslant -1 \]
    right ; linarith
    --\[ x \geqslant -\frac{1}{3} \]
    --I need to verify that $x \geq -\frac{1}{3}$ is a valid solution.
    intro a
    rcases a with h1 | h2
    exfalso ; linarith
    linarith
    push_neg at h
    rw [abs_eq_neg_self.2 (le_of_lt h)]
    --Case 2: If $2x+3 < 0$, which means $x < -\frac{3}{2}$, we have to reverse the inequality sign when we take away the absolute value, so the inequality becomes:
    --\[ x - (2x + 3) \geqslant 2 \]
    constructor
    intro leq
    have : - x + 3 ≥ 2 := by linarith
    --\[ -x - 3 \geqslant 2 \]
    have : - x ≥ 5 := by linarith
    --\[ -x \geqslant 5 \]
    left ; linarith
    --\[ x \leqslant -5 \]
    --I need to verify that $x \leq -5$ is a valid solution.
    intro a
    rcases a with h1 | h2
    linarith
    exfalso ; linarith

--Comment: I don't fully follow the solution, as there is no theorem in Mathlib4 stating that the union would provide the answer.
