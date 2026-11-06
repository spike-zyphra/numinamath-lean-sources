import Mathlib

theorem number_theory_95568 : (∑ i in Finset.Icc 1 99, Nat.factorial i) % 10 = 3 := by 
  native_decide