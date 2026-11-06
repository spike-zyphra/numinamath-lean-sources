import Mathlib

theorem number_theory_251341 :
    (∑ n in (Finset.Icc 1000 9999).filter (fun n => (Nat.digits 10 n).sum = 4 ∧ Odd n), n) % 1000 = 449 := by
  native_decide