import Mathlib

theorem algebra_236409 : (∑ i ∈ Finset.range 10, (2 * i + 2)) / (∑ i ∈ Finset.range 10, (i + 1)) = 2 := by 
  norm_num [Finset.sum_range_succ]