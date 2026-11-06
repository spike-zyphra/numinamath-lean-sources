import Mathlib

theorem number_theory_5081 :
    ∑ x in (Nat.divisors 1029864).filter (fun y => y.Prime ∧ (Nat.digits 10 y).length = 2), x = 141 := by
  native_decide