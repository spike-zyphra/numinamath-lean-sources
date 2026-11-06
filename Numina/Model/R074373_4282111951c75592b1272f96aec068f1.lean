import Mathlib

theorem algebra_3693 : ∑ i ∈ Finset.range 10, (3 * i + 3) ^ 3 = 81675 := by 
  norm_num [Finset.sum_range_succ]