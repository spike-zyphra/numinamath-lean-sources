import Mathlib

theorem algebra_10571 : ∑ i ∈ Finset.range 20, (- (2 : ℤ) * i - 1) = -400 := by 
  norm_num [Finset.sum_range_succ]