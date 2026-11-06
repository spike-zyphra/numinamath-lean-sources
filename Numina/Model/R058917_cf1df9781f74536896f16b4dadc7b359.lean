import Mathlib

theorem algebra_214251 :
    (∑ i ∈ Finset.range 15, (2 * i + 1)) - (∑ j ∈ Finset.range 10, (2 * j + 2)) = 115 := by
  norm_num [Finset.sum_range_succ]