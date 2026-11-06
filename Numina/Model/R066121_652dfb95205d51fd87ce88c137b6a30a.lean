import Mathlib

theorem algebra_288310 : ∑ i in Finset.range 8, (i + 1) = 6^2 := by 
  norm_num [Finset.sum_range_succ]