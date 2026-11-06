import Mathlib

/-
Problem

The solutions to the equation $x(5x+2) = 6(5x+2)$ are ___.
-/

/-
Solution

To solve the equation, let's first move all terms to one side to get:
$$x(5x+2) - 6(5x+2) = 0.$$
Next, we factor by grouping:
$$(x-6)(5x+2) = 0.$$
From the Zero Product Property, if the product of two factors is zero, then at least one of the factors must be zero. Thus, we have two possibilities:
$$x - 6 = 0 \quad \text{or} \quad 5x + 2 = 0.$$
Solving each equation for $x$ gives us the solutions:
$$x = 6 \quad \text{and} \quad x = -\frac{2}{5}.$$
Therefore, the solutions to the equation are $x = \boxed{6}$ and $x = \boxed{-\frac{2}{5}}$.
-/

theorem algebra_9329 (x : ℝ) : x * (5 * x + 2) = 6 * (5 * x + 2) ↔ x = 6 ∨ x = -2 / 5 := by
  constructor
  · intro foo
    -- proof by contradiction
    by_contra h
    push_neg at h
    obtain ⟨n1, n2⟩ := h
    -- since $x \neq -2/5$
    have : 5 * x + 2 ≠ 0 := by
      intro bar
      apply n2
      field_simp
      apply_fun (· - 2) at bar
      simp only [add_sub_cancel_right, zero_sub] at bar
      rw [← bar]
      ring
    apply_fun (· * 1 / (5 * x + 2)) at foo
    -- simplification
    field_simp at foo
    exact n1 foo
  · -- trivial calculation
    intro foo
    rcases foo with h | k
    · rw [h]
    · rw [k]
      ring