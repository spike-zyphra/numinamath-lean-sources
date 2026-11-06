import Mathlib

theorem number_theory_232946 : (∑ i in Finset.Icc 1 10, Nat.factorial i) % 5 = 3 := by
  native_decide