import Mathlib

/- Determine the value of $-1 + 2 + 3 + 4 - 5 - 6 - 7 - 8 - 9 + \dots + 10000$, where the signs change after each perfect square. -/
theorem algebra_11048 : ∑ i ∈ Finset.range 10000, (-1 : ℤ)^ (Nat.sqrt i + 1) * (i + 1) = 1000000 := by native_decide
