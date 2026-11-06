import Mathlib

theorem algebra_11769 : (∑ i in Finset.range 20, (2 * i + 2)) - (∑ i in Finset.range 15, (2 * i + 1)) = 195 := by
  norm_num [Finset.sum_range_succ]