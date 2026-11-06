import Mathlib

theorem algebra_3402 : ∑ i ∈ Finset.range 18, (i + 1) * (i + 2) = 2280 := by 
  norm_num [Finset.sum_range_succ]