import Mathlib

theorem algebra_11048 : ∑ i ∈ Finset.range 10000, (-1 : ℤ)^ (Nat.sqrt i + 1) * (i + 1) = 1000000 := by
  native_decide