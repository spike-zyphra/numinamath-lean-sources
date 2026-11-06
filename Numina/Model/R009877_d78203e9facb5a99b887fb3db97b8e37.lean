import Mathlib

theorem calculus_141617 (C : ℝ) (y : ℝ → ℝ) (hy : y = fun x => x^2 + C) :
    Differentiable ℝ y ∧ ∀ x, deriv y x = 2 * x ∧ ((y 1 = 2) ↔ C = 1) := by
  constructor
  · -- To check differentiability of function $y$, it's differentiable since $x^2$ and $C$ (a constant function) are differentiable functions
    rw [hy]
    apply Differentiable.add
    · exact differentiable_pow 2
    · exact differentiable_const C
  · intro x
    constructor
    · -- Compute derivative at $x$, from Mathlib we have derivative of $x^2$ is $2x$ and derivative of constant $C$ is $0$, so derivative of $x^2+C$ is $2x+0=2x$ as required
      rw [hy]
      simp [deriv_add, deriv_pow, deriv_const]
      all_goals linarith
    · -- Verify initial condition $(1, 2)$
      rw [hy]
      simp
      constructor
      · -- Forward: If $y(1) = 2 \Rightarrow C = 1$
        intro h
        linarith
      · -- Backward: If $C = 1 \Rightarrow y(1) = 2$
        intro h
        linarith