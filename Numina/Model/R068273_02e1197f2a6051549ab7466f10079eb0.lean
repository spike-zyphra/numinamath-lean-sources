import Mathlib

open Finset Real

theorem algebra_3071 : ∑ i ∈ range 2018, (1 / ((i + 1) * (i + 2) * (i + 3)) : ℝ) = 2039189 / 8156760 := by
  norm_num [sum_range_succ]
  <;> native_decide