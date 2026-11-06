import Mathlib

theorem algebra_21349 : ⌈(⌊(52 / 3 : ℝ)⌋ / (5 / 23 :ℝ))⌉ = 79 := by
  norm_num [Int.floor_eq_iff, Int.ceil_eq_iff]