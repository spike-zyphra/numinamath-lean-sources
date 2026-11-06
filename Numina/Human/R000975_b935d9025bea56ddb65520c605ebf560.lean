import Mathlib

/- What is the product of the positive integer divisors of 100? -/
theorem number_theory_19502 : ∏ d ∈ (100 : ℕ).divisors, d = 1000000000 := by 
  rfl