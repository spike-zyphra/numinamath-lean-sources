import Mathlib

theorem algebra_16554 : ⌈(12 / 7 * -29 / 3 : ℝ)⌉ - ⌊((12 / 7 : ℝ) * ⌊(-29 / 3 : ℝ)⌋)⌋ = 2 := by
  norm_num [Int.ceil_eq_iff, Int.floor_eq_iff]