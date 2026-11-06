import Mathlib

/- Find the remainder when $1^3 + 2^3 + 3^3 + \dots + 100^3$ is divided by 6. -/
theorem number_theory_17170 : (∑ i in Finset.Icc 1 100, i^3) % 6 = 4 := by
  rfl