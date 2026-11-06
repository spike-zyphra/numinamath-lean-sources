import Mathlib

theorem number_theory_11288 : 10 * 901 ≡ 1 [ZMOD 1001] := by 
  norm_num [Int.ModEq]