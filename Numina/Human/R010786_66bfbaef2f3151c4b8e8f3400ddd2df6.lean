import Mathlib

/- What is the greatest common divisor of 128, 144 and 480? -/
theorem algebra_17112 : gcd (gcd 128 144) 480 = 16 := by
  decide