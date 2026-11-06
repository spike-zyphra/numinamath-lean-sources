import Mathlib

theorem number_theory_199333 : (∑ i in Finset.Icc 1 1987, i^5) % 25 = 8 := by
  native_decide