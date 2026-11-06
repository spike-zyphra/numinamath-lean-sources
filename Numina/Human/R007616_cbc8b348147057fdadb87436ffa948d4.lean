import Mathlib

/- Solve the equation: $x^{2}-6x+5=0$. -/
theorem algebra_9472 (x : ℝ) (hx : x^2 - 6 * x + 5 = 0) : x = 1 ∨ x = 5 := by
  -- factorize the equation, x^2-6x+5=(x-5)(x-1)
  have: x ^ 2 - 6 * x + 5 = (x-5)*(x-1) := by ring
  rw [this] at hx
  -- (x-5)(x-1) = 0 leads to x=5 or x=1, exactly two roots of the equation.
  have eq': x-5 = 0 ∨ x - 1 = 0 := mul_eq_zero.mp hx
  rcases eq' with e5 | e1
  right
  rw [← add_zero 5, ← e5]
  simp
  left
  rw [← add_zero 1, ← e1]
  simp