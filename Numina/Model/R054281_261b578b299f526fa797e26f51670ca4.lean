import Mathlib

open Finset Real

theorem algebra_5878 : ∑ i ∈ range 19, (1 / ((i + 1) * (i + 3))) = 19 / 40 := by
  norm_num [Finset.sum_range_succ]