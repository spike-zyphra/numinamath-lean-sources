import Mathlib

/- What is the greatest common divisor of $2^{1001}-1$ and $2^{1012}-1$? -/
theorem number_theory_15219 : Nat.gcd (2^1001 - 1) (2^1012 - 1) = 2047 := by
  norm_num
  <;> rfl