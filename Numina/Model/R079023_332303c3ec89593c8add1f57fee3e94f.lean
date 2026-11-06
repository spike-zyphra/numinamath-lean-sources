import Mathlib

theorem number_theory_296988 : (∑ i in Finset.Icc 1 250, Nat.factorial i * i) % 2008 = 2007 := by
  native_decide