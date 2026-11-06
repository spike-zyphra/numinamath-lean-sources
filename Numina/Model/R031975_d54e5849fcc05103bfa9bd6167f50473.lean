import Mathlib

theorem number_theory_287413 : (∑ i in Finset.Icc 1 9, i^i) % 3 = 1 := by
  native_decide