import Mathlib

theorem algebra_14162 : ⌊(⌈((13 / 7 : ℝ)^2)⌉ + 17 / 4 : ℝ)⌋ = 8 := by
  norm_num [Int.floor_eq_iff, Int.ceil_eq_iff]