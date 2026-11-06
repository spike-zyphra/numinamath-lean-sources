import Mathlib

theorem algebra_17173 : ∑ i ∈ Finset.Icc 1 500, (Nat.digits 10 i).count 9 = 100 := by 
  native_decide