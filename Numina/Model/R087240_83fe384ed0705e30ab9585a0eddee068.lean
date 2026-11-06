import Mathlib

theorem algebra_98046 :
    (∑ i in Finset.range 80, (i * 2 + 2)) - (∑ i in Finset.range 80, (i * 2 + 1)) = 80 := by
  norm_num [Finset.sum_range_succ]