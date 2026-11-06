import Mathlib

theorem algebra_12397 : ⌊( -2.54 : ℝ)⌋ + ⌈( 25.4 : ℝ)⌉ = 23 := by
  norm_num [Int.floor_eq_iff, Int.ceil_eq_iff]