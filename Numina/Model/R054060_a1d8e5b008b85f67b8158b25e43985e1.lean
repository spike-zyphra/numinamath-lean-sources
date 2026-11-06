import Mathlib

theorem algebra_5726 : ∑ i ∈ Finset.range 29, (i + 3) * (i + 4) * (i + 5) = 278226 := by 
  norm_num [Finset.sum_range_succ]