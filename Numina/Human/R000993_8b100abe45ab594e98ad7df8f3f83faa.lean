import Mathlib

/- There are real numbers $A$ and $B$ such that
\[\frac{5x-16}{x^2-7x+10}=\frac{A}{x-2}+\frac{B}{x-5}.\]Find $A+B$. -/
theorem algebra_19628 {A B : ℝ} (h : ∀ x, x ≠ 2 ∧ x ≠ 5 → (5 * x - 16) / (x ^ 2 - 7 * x + 10) = A / (x - 2) + B / (x - 5)) :
    A + B = 5 := by
  have h₁ := h 3
  have h₂ := h 6
  norm_num at h₁ h₂
  linarith
