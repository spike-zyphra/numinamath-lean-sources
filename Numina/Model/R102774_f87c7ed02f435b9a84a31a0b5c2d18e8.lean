import Mathlib

theorem algebra_11779 : ⌊(2005^3 : ℝ) / (2003 * 2004) - (2003^3 : ℝ) / (2004 * 2005)⌋ = 8 := by
  norm_num [Int.floor_eq_iff]