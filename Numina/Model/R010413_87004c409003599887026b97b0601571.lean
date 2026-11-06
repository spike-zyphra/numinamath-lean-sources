import Mathlib

theorem algebra_634142 : ∑ i in Finset.range 15, (3 * i + 5) ^ 2 = 12660 := by 
  norm_num [Finset.sum_range_succ]