import Mathlib

open Finset Real

theorem algebra_79 : ∏ i ∈ range 98, (1 + 1 / ((i + 1) * (i + 3))) = 99 / 50 := by
  norm_num [prod_range_succ]