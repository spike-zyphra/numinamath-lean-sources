import Mathlib

open Finset

theorem algebra_3321 : ∑ i ∈ range 10, (1 / ((3 * (i + 1)) * (i + 1) * (3 * (i + 1) + 1))) = 65 / 2376 := by
  norm_num [sum_range_succ]