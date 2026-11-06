import Mathlib

theorem number_theory_10078 : ∑ n in (Finset.Icc 1 82), (Nat.digits 10 n).sum = 667 := by 
  native_decide