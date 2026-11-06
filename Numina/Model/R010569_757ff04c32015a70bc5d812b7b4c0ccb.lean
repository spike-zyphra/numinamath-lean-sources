import Mathlib

theorem algebra_13197 : (∑ n in Finset.range 669, (-1 : ℤ)^n * Nat.choose 2004 (3 * n)) % 1000 = 6 := by 
  native_decide