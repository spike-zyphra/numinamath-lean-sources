import Mathlib

open Finset Real

theorem algebra_3054 : ∑ i ∈ range 9, (10^2 * 10^i) / ((10^(i + 1)) * (10^(i + 2))) = 9 / 10 := by
  norm_num [sum_range_succ]