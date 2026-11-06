import Mathlib

theorem number_theory_4012 : ((Finset.Ico 1 72).filter fun n => Nat.Coprime n 72).card = 24 := by
  native_decide