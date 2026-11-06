import Mathlib

theorem algebra_15722 : ⌈((108 * (1- 0.25)) * 2 / 15 : ℝ)⌉ = 11 := by
  norm_num [Int.ceil_eq_iff]