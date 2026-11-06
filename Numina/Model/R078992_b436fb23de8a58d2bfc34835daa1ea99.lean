import Mathlib

theorem number_theory_239422 :
    ∑ n in Finset.Icc 1 100, (Nat.digits 10 n).count 7 = 20 := by 
  native_decide