import Mathlib

/- What is the sum of the positive whole number divisors of 210? -/
theorem number_theory_15047 : ∑ d in (210 : ℕ).divisors, d = 576 := by
  rfl