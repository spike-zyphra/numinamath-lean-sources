import Mathlib

/- Give the greatest common divisor of $6^3$ and $3^6$. -/
theorem algebra_21125 : Nat.gcd (6^3 : ℕ) (3^6 : ℕ) = 27 := by
  norm_cast
