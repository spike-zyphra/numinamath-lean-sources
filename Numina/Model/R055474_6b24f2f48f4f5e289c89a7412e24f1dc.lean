import Mathlib

open Finset Real

theorem inequalities_119838 : ∏ i ∈ range 50, (2 * (i + 1)) / ((2 * i + 1) : ℝ) > 10 := by
  norm_num [prod_range_succ, mul_div_mul_left]