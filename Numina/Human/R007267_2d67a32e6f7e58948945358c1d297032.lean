import Mathlib

/- Jack rewrites the quadratic $9x^2 - 30x - 42$ in the form of $(ax + b)^2 + c,$ where $a,$ $b,$ and $c$ are all integers. What is $ab$? -/
theorem algebra_13906 {a b c : ℤ} (ha : a ≠ 0) (h : ∀ x, 9 * x ^ 2 - 30 * x - 42 = (a * x + b) ^ 2 + c) :
    a * b = -15 := by
  have h₁ := h 1
  have h₂ := h (-1)
  have h₃ := h 2
  have h₄ := h (-2)
  linarith