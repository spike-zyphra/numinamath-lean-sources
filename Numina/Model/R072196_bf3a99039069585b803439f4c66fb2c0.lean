import Mathlib

theorem algebra_10534 : ∑ i in Finset.range 49, (i + 1) = 1225 := by 
  norm_num [Finset.sum_range_succ]