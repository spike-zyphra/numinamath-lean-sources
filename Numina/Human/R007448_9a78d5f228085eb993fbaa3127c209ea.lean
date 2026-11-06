import Mathlib

/- Factorize the polynomial $b^2 - c^2 + a(a + 2b)$ within the range of rational numbers. -/
theorem algebra_9429 {a b c : ℚ} : b^2 - c^2 + a * (a + 2 * b) = (a + b + c) * (a + b - c) := by
  -- Equality in ring
  ring
