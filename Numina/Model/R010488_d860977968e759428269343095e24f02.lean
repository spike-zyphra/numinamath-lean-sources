import Mathlib

theorem number_theory_14622 : ((Finset.Icc 100 999).filter fun n => (Nat.digits 10 n).Nodup).sum id % 1000 = 680 := by 
  native_decide