import Mathlib

theorem number_theory_95466 :
    (Nat.digits 10 (∑ s in (Finset.Ico 1 100).filter (fun x => x % 2 = 0 ∧ x % 5 = 4), s)).sum = 13 := by
  native_decide