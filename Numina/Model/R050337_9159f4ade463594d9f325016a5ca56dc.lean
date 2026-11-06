import Mathlib

open Finset Real

theorem algebra_3601 : ∑ i ∈ range 12, (i + 3) / ((i + 1) * (i + 3) * (i + 4)) = 2209 / 4095 := by
  norm_num [sum_range_succ]