import Mathlib

/- What is the sum of all of the odd divisors of $180$? -/
theorem number_theory_17146 : ∑ d in (Nat.divisors 180).filter Odd, d = 78 := by
  rfl