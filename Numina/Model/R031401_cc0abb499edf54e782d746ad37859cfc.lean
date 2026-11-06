import Mathlib

theorem inequalities_212461 :
    ∑ i ∈ Finset.range 98, (1 / (Nat.fib i * Nat.fib (i + 2) : ℚ)) < 1 := by
  native_decide