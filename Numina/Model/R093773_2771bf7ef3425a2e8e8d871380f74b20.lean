import Mathlib

open Finset Real

theorem algebra_16324 : ∏ i ∈ range 667, ((3 * (i + 1)) / (3 * (i + 2))) = 1 / 668 := by
  norm_num [prod_range_succ]