import Mathlib

theorem number_theory_12975 : (∑ n in (Finset.Icc 1000 9999).filter fun n => (Nat.digits 10 n).sum = 8, n) = 353310 := by 
  native_decide