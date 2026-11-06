import Mathlib

/- How many distinct prime factors does the sum of the positive divisors of $400$ have? -/
theorem number_theory_13182 : (Nat.primeFactors (∑ d in (400 : ℕ).divisors, d)).card = 1 := by
  native_decide
