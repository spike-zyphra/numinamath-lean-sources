import Mathlib

theorem algebra_141057 : ∑ i ∈ Finset.Icc 19 1999, i * (i + 1) * (i + 2) = 6 * (Nat.choose 2002 4 - Nat.choose 21 4) := by 
  native_decide