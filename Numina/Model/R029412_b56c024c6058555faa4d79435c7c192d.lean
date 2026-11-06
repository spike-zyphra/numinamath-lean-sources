import Mathlib

theorem algebra_207505 {a b : ℤ} : (a^3 - b^3) ∣ (a^2 - b^2) * (a + b)^4 - (a^5 + b^5) * (a - b) := by
  use 5 * a * b * (a + b)
  ring