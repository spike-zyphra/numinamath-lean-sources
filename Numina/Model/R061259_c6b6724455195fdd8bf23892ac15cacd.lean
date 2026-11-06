import Mathlib

open Real
open scoped BigOperators

theorem algebra_5173 : ∑ i ∈ Finset.range 19, (1 / ((i + 1) * (i + 4))) = 2603 / 4620 := by 
  norm_num [Finset.sum_range_succ]