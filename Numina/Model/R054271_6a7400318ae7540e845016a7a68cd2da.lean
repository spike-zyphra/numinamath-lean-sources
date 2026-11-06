import Mathlib

theorem number_theory_2519 :
    ∑ x in (Nat.divisors 120).filter (fun y => ¬Nat.Prime y ∧ ¬Odd y), x = 334 := by
  native_decide