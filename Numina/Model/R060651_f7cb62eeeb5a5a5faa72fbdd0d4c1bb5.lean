import Mathlib

theorem algebra_323244 : ⌊(3^100 + 2^100 : ℝ) / (3^96 + 2^96)⌋ = 80 := by
  norm_num [Int.floor_eq_iff]