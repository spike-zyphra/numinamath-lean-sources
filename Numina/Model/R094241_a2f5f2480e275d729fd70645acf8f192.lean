import Mathlib

theorem algebra_92997: ∑ i in Finset.range 50, (-1 : ℤ)^i * (100 - 2 * i) = 50 := by 
  norm_num [Finset.sum_range_succ]