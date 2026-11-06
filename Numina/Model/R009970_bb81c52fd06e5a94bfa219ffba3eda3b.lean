import Mathlib

theorem number_theory_11639 : ((Finset.Icc 100 999).filter fun n => IsSquare n ∧ Nat.digits 10 n =
    (Nat.digits 10 n).reverse).card = 3 := by 
  native_decide