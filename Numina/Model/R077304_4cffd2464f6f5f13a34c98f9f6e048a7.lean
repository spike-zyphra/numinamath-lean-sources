import Mathlib

open Finset Real

theorem algebra_292885 : ∏ i ∈ range 2020, (1 + (-1 : ℝ)^i / (i + 1)) = 1 := by 
  norm_num [prod_range_succ]