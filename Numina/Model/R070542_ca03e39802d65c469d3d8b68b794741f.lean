import Mathlib

open Finset Real

theorem algebra_256189 : ∑ i ∈ range 128, (1 / ((2 * i + 1) * (2 * i + 3) : ℚ)) = 128 / 257 := by
  norm_num [sum_range_succ]