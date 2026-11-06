import Mathlib

theorem algebra_11208 : ∑ i ∈ Finset.range 9, (2 * i + 1) = 81 := by 
  norm_num [Finset.sum_range_succ]