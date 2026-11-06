import Mathlib

/- Simplify: $\frac{2^{n+4} - 2(2^n)}{2(2^{n+3})}$. Express your answer as a common fraction. -/
theorem algebra_14585 (n : ℕ) : (2 ^ (n + 4) - 2 * (2 ^ n)) / (2 * (2 ^ (n + 3))) = (7 / 8: ℝ) := by
  field_simp
  ring_nf
