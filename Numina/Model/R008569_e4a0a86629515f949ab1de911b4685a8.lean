import Mathlib

theorem number_theory_23249 : 24 * 116 ≡ 1 [ZMOD 11 ^ 2] := by 
  norm_num [Int.ModEq, pow_two]