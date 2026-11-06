import Mathlib

/- Find the modulo $7$ remainder of the sum $1+3+5+7+9+\dots+195+197+199.$ -/
theorem number_theory_22787 : (∑ i in Finset.range 100, (2 * i + 1)) % 7 = 4 := by
  rfl