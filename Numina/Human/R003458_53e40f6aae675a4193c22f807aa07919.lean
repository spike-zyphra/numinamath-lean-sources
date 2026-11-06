import Mathlib

theorem number_theory_184359 : ⌊(10000 * (5568 / 10000 : ℝ))⌋ = 5568 := by 
  norm_num [Int.floor_eq_iff]