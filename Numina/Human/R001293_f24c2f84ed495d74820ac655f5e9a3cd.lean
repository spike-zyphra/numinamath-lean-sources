import Mathlib

/- Find the units digit of the sum of the first $21$ positive perfect cubes. -/
theorem number_theory_22946 : (∑ i ∈ Finset.range 21, (i + 1)^3) % 10 = 1 := by 
  rfl