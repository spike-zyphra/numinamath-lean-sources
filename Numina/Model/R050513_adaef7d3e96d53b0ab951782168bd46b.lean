import Mathlib

theorem algebra_12219 : ∑ i ∈ Finset.range 50, (Nat.digits 10 (i + 1)).count 9 = 5 := by
  native_decide