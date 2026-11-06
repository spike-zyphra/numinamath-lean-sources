import Mathlib

/- What is the sum of all of the positive even factors of $504$? -/
theorem number_theory_12578 : ∑ x in (504 : ℕ).divisors.filter Even, x = 1456 := by 
  rfl