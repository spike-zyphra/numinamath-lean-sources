import Mathlib

open Finset Real

theorem algebra_213348 : ∑ i ∈ range 2002, (1 / ((i + 1) * (i + 2)) : ℝ) = 2002 / 2003 := by
  norm_num [sum_range_succ]