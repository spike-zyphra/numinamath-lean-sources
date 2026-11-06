import Mathlib

theorem number_theory_187734 : Nat.factorial 2002 / (∑ i in Finset.Icc 1 2001, Nat.factorial i) = 2000 := by
  native_decide