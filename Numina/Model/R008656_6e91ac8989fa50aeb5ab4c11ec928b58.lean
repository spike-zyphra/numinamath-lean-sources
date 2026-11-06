import Mathlib

theorem number_theory_4783 : 3^10 ≡ 1 [ZMOD 11^2] := by 
  norm_num [Int.ModEq]