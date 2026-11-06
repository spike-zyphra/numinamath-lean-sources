import Mathlib

theorem number_theory_17018 : ((Finset.Icc 2 100).filter fun n => 7 ∣ Nat.ofDigits n [6, 3, 2, 5, 3, 2]).card = 14 := by 
  native_decide