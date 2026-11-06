import Mathlib

theorem number_theory_327589 : ∑ n in Finset.Icc 1000 1996, (Nat.digits 10 n).sum = 14419 := by 
  native_decide