import Mathlib

theorem number_theory_4784 : 3^100 ≡ 4 [ZMOD 7] := by 
  norm_num [Int.ModEq]