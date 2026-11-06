import Mathlib

theorem algebra_13639 : ⌈(5 / 4 : ℝ)⌉ + ⌊-5 / 4⌋ = 0 := by 
  norm_num [Int.ceil_eq_iff, Int.floor_eq_iff]