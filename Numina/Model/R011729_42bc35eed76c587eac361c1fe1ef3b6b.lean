import Mathlib

open Real
open scoped BigOperators

theorem inequalities_157188 : ∑ i in Finset.range 30, (i + 1) / (2 ^ (i + 1)) < 2 := by
  norm_num [Finset.sum_range_succ]