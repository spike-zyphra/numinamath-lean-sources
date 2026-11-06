import Mathlib

theorem number_theory_313800 : (∑ i in Finset.range 1989, (-1 : ℤ)^i * (i + 1)^2) % 1991 = 1 := by
  native_decide