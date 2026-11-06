import Mathlib

open Finset Real

theorem algebra_4994 : (∑ i ∈ range 10, (1 / ((2 * i + 1) : ℚ) - 1 / ((2 * i + 2) : ℚ))) / ∑ i ∈ range 10, (1 / ((2 * i + 22) : ℚ)) = 2 := by
  norm_num [Finset.sum_range_succ]