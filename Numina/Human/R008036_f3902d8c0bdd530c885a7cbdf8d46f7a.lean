import Mathlib

/- What is the sum of the positive odd divisors of $60$? -/
theorem algebra_12666 : ∑ d in (60 : ℕ).divisors.filter Odd, d = 24 := by 
  rfl