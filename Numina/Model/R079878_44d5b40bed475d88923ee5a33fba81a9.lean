import Mathlib

open Finset Real

theorem algebra_6915 : ∑ i ∈ range 9, (1 / ((i + 1) * (i + 2) * (i + 3) * (i + 4))) = 73 / 1320 := by 
  norm_num [sum_range_succ]
  <;> try { native_decide }