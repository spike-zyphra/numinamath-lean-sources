import Mathlib

/- Find constants $A,$ $B,$ and $C$ so that
\[\frac{4x}{(x - 5)(x - 3)^2} = \frac{A}{x - 5} + \frac{B}{x - 3} + \frac{C}{(x - 3)^2}.\]Enter the ordered triple $(A,B,C).$ -/
theorem algebra_15981 {A B C : ℝ} (h : ∀ x, 4 * x / ((x - 5) * (x - 3) ^ 2) = A / (x - 5) + B / (x - 3) + C / (x - 3) ^ 2) :
    A = 5 ∧ B = -5 ∧ C = -6 := by
  have := h 4
  have := h 6
  have := h 2
  norm_num at *
  exact ⟨by linarith, by linarith, by linarith⟩