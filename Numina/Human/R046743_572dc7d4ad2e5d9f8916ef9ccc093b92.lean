import Mathlib

/- Find $A$ and $B$ such that
\[\frac{5x+2}{x^2-7x-30}=\frac{A}{x-10}+\frac{B}{x+3}.\]Write your answer in the form $(A,B)$. -/
theorem algebra_12962 {A B : ℝ} (h : ∀ x, x ^ 2 - 7 * x - 30 ≠ 0 → x - 10 ≠ 0 → x + 3 ≠ 0 → (5 * x + 2) / (x ^ 2 - 7 * x - 30) = A / (x - 10) + B / (x + 3)) :
    (A, B) = (4, 1) := by
  have := h 0
  have := h 1
  have := h 2
  have := h 3
  norm_num at *
  constructor
  <;> linarith