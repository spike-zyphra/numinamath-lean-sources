import Mathlib

theorem algebra_279427 : ∑ i in Finset.range 100, (i + 1) * 10 = 50500 := by 
  norm_num [Finset.sum_range_succ]