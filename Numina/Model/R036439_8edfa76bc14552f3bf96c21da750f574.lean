import Mathlib

theorem algebra_16826 : ∑ i ∈ Finset.range 50, (-1 : ℤ)^i * Nat.choose 99 (2 * i) = -2^49 := by 
  native_decide