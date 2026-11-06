import Mathlib

open Finset Real

theorem algebra_3192: ∑ i ∈ range 19, (2 / ((i + 1) * (i + 2) * (i + 3) : ℝ)) = 209 / 420 := by
  norm_num [sum_range_succ]