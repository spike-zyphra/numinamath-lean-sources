import Mathlib

theorem number_theory_807 : ((Finset.Icc 1 209).filter fun n => Nat.Coprime n 209).card = 180 := by 
  native_decide