import Mathlib

theorem number_theory_96807 :
    (Nat.digits 10 (∑ s in (Finset.Icc 1 100).filter (fun x => x % 2 = 0 ∧ x % 5 = 4), s)).sum = 13 := by 
  native_decide