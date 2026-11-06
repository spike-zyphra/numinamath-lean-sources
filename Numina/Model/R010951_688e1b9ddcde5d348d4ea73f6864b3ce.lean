import Mathlib

theorem number_theory_619566 : ((Finset.Icc 1 2000).filter fun n => Odd (Nat.divisors n).card).card = 44 := by 
  native_decide