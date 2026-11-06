import Mathlib

theorem algebra_10888 : ⌈(-5 / 3 : ℝ) ^ 2⌉ = 3 := by
  norm_num [Int.ceil_eq_iff]