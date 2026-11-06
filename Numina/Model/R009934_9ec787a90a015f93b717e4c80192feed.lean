import Mathlib

theorem number_theory_12305 :
    ∑ n in (Finset.Icc 1 100).filter (fun n => List.reverse (Nat.digits 7 n) = Nat.digits 16 n), n = 58 := by
  native_decide