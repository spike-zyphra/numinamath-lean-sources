import Mathlib

/- Suppose
\[\frac{1}{x^3-x^2-21x+45}=\frac{A}{x+5}+\frac{B}{x-3} + \frac{C}{(x - 3)^2}\]where $A$, $B$, and $C$ are real constants. What is $A$? -/
theorem algebra_13062 {A B C : ℝ} (h : ∀ x, x ≠ 3 ∧  x ≠ -5 ∧ 1 / (x ^ 3 - x ^ 2 - 21 * x + 45) = A / (x + 5) + B / (x - 3) + C / (x - 3) ^ 2) :
    A = 1 / 64 := by
  have h₁ := h 1
  have h₂ := h (-1)
  have h₃ := h 4
  norm_num at *
  linarith