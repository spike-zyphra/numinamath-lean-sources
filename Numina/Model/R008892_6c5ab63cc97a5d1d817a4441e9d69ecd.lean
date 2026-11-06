import Mathlib

open Real

theorem algebra_15501 : 2002 + (∑ n ∈ Finset.range 2000, ((1 : ℝ)/ 2 ^ (n + 1)) * (2001 - n)) = 4002 := by
  norm_num [Finset.sum_range_succ]