import Mathlib

theorem number_theory_37717 :
    ∑ n in (Finset.Icc 100 999).filter (fun n => Nat.digits 10 n = (Nat.digits 10 n).reverse ∧ 4 ∣ (Nat.digits 10 n)[1]! ∧ 11 ∣ n), n = 726 := by 
  native_decide