import Mathlib

/- In a rectangular coordinate system, the line $5y = 2x$ intersects the line $3x - 4y = 7$ at point $Z$. What is the sum of the coordinates of point $Z$? -/
theorem algebra_19773 {x y : ℝ} (h : 5 * y = 2 * x ∧ 3 * x - 4 * y = 7) :
    x + y = 7 := by
  have h₁ := h.1
  have h₂ := h.2
  linarith