import Mathlib

theorem algebra_20832 : ⌈(7 / 4 : ℝ) ^ 2⌉ ^ 2 = 16 := by 
  norm_num [Int.ceil_eq_iff]