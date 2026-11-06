import Mathlib

theorem number_theory_17170 : (∑ i in Finset.Icc 1 100, i^3) % 6 = 4 := by 
  native_decide