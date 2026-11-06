import Mathlib

theorem number_theory_3128: (∑ i in Finset.range 2020, (i+1)) % 11 = 6 := by
  native_decide