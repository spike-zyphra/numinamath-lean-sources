import Mathlib

theorem algebra_254035 : (Nat.choose 1996 4) = ∑ i ∈ Finset.Icc 3 1995, Nat.choose i 3 := by 
  native_decide