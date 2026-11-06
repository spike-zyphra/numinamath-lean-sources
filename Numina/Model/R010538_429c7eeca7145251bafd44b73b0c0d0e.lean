import Mathlib

theorem number_theory_17052 : (∑ i in Finset.Icc 1 2006, Nat.factorial i) % 10 = 3 := by
  native_decide