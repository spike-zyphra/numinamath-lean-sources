import Mathlib

theorem algebra_10734 : ⌊|(-4.2 : ℝ)|⌋ + |⌊(-4.2 : ℝ)⌋| = 9 := by 
  norm_num [Int.floor_eq_iff, abs]