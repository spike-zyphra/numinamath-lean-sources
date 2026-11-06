import Mathlib

theorem number_theory_240538 : ∑ x in (Nat.divisors 290224).filter (fun y => y ∈ Finset.Icc 10 99), x = 397 := by
  native_decide