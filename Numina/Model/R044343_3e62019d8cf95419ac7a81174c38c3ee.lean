import Mathlib

def a : ℕ → ℤ
| 0 => 1
| 1 => 3
| n + 2 => a (n + 1) - a n

theorem algebra_249994 : ∑ i in Finset.range 100, a i = 5 := by 
  norm_num [Finset.sum_range_succ, a]