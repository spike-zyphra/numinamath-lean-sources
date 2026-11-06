import Mathlib

open Finset Real

theorem algebra_231 : (∑ i ∈ range 100, (-1 : ℝ)^i * (i + 1) * 2 * (i + 1) * 4 * (i + 1)) / (∑ i ∈ range 100, (i + 1) * 3 * (i + 1) * 9 * (i + 1)) = -1624 / 275427 := by 
  norm_num [sum_range_succ]