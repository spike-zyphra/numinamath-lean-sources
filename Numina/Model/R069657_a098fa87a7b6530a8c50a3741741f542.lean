import Mathlib

theorem number_theory_103182 : ⌊(10^93 / (10^31 + 3 : ℝ))⌋ % 100 = 8 := by
  norm_num [Int.floor_eq_iff]