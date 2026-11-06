import Mathlib

/- Given the system of equations in terms of $x$ and $y$: $\left\{\begin{array}{l}{x-y=a+3}\\{2x+y=5a}\end{array}\right.$, where the solution satisfies $x \lt y$, find the range of values for $a$. -/
theorem algebra_9010 (a : ℝ) : (∃ x y, x - y = a + 3 ∧ 2 * x + y = 5 * a ∧ x < y) ↔ a < -3 := by
  -- Prove the two directions separately
  constructor <;> intro h
  . obtain ⟨x, y, h1, h2, h3⟩ := h
    -- Solve the equations using linarith
    replace ⟨h1, h2⟩ : x = 2 * a + 1 ∧ y = a - 2 := by constructor <;> linarith
    -- Solve the linear inequality using linarith
    subst x y
    linarith
  . -- Plug in what we solved in the forward direction
    use 2 * a + 1, a - 2
    refine ⟨?_, ?_, ?_⟩ <;> linarith
