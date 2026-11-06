import Mathlib

/- There are values $A$ and $B$ such that
\[\frac{Bx-11}{x^2-7x+10}=\frac{A}{x-2}+\frac{3}{x-5}.\]Find $A+B$. -/
theorem algebra_10870 {A B : ℝ} (h : ∀ x, x ≠ 2 → x ≠ 5 →  (B * x - 11) / (x ^ 2 - 7 * x + 10) = A / (x - 2) + 3 / (x - 5)) :
    A + B = 5 := by
  have h₁ := h 1
  have h₂ := h 2
  have h₃ := h 4
  norm_num at h₁ h₂ h₃
  linarith
