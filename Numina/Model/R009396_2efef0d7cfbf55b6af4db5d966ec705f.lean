import Mathlib

theorem algebra_15469 : ∑n ∈ (Finset.Icc 10 99), (Nat.digits 10 n).count 6 = 19 := by
  native_decide