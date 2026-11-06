import Mathlib

theorem number_theory_238916 : (∑ i in Finset.range 2017, 3 ^ i) % 4 = 1 := by 
  native_decide