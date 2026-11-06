import Mathlib

theorem number_theory_12552 :
    ∑ n in (Finset.Icc 10 99).filter (fun n => n % (Nat.digits 10 n).sum = 0 ∧ n % (Nat.digits 10 n).prod = 0), n = 72 := by
  native_decide