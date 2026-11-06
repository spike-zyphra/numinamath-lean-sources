import Mathlib

def a : ℕ → ℕ
| 0 => 1
| 1 => 2
| n + 2 => a n + a (n + 1)

theorem algebra_8269 : (∏ i ∈ Finset.range 98, a (i + 2) / a (i + 1)) = 1 := by
  norm_num [Finset.prod_range_succ, a]