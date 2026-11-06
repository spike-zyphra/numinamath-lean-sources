import Mathlib

theorem number_theory_15901 : (∑ i in Finset.range 123, (i + 1)) % 5 = 1 := by 
  native_decide