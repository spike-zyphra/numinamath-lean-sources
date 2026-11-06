import Mathlib

open Finset

theorem algebra_97307 {a : ℕ → ℤ}
    (ha : ∀ i, a i = (-1 : ℤ)^i * (1990 - 10 * i)) : ∑ i ∈ range 200, a i = 1000 := by 
  norm_num [Finset.sum_range_succ, ha]