import Mathlib

theorem inequalities_212461 :
    ∑ i ∈ Finset.range 98, (1 / (Nat.fib i * Nat.fib (i + 2) : ℚ)) < 1 := by 
  norm_num [Finset.sum_range_succ]