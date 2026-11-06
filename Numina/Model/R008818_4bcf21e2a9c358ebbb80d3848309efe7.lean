import Mathlib

theorem algebra_15732 : ⌈(((45 / 33.8) * 1000) / 200 : ℝ)⌉ = 7 := by 
  norm_num [Int.ceil_eq_iff]