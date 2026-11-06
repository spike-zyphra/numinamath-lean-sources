import Mathlib

/- If the product $(3x^2 - 5x + 4)(7 - 2x)$ can be written in the form $ax^3 + bx^2 + cx + d$, where $a,b,c,d$ are real numbers, then find $8a + 4b + 2c + d$. -/
theorem algebra_15813 (a b c d : ℝ) (h : ∀ x, (3 * x ^ 2 - 5 * x + 4) * (7 - 2 * x) = a * x ^ 3 + b * x ^ 2 + c * x + d) :
    8 * a + 4 * b + 2 * c + d = 18 := by 
  have h₁ := h 1
  have h₂ := h 2
  have h₃ := h 3
  have h₄ := h 4
  linarith