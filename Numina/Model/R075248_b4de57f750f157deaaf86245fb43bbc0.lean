import Mathlib

theorem number_theory_183472 : ⌊(10^93 : ℝ) / (10^31 + 3)⌋ % 100 = 8 := by
  norm_num [Int.floor_eq_iff]