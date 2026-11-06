import Mathlib

open Finset

theorem number_theory_9184 : (∑ i ∈ range 2014, ⌊(8^(i + 1))/(9 : ℝ)⌋) % 63 = 56 := by
  norm_num [sum_range_succ]
  <;> native_decide