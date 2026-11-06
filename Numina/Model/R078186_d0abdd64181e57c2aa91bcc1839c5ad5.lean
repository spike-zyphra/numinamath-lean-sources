import Mathlib

theorem number_theory_137320 :
    (∑ i ∈ Finset.Icc 1 2020, (Nat.digits 10 i).count 1) -
    (∑ i ∈ Finset.Icc 1 2020, (Nat.digits 10 i).count 0) = 1089 := by
  native_decide