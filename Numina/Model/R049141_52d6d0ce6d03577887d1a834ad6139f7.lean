import Mathlib

theorem algebra_20125 : ⌈(7/4 : ℝ)^2⌉ = 4 := by
  norm_num [Int.ceil_eq_iff]