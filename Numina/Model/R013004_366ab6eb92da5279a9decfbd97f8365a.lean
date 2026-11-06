import Mathlib

theorem number_theory_5924: 9^2022 + 2022 ≡ 138 [ZMOD 299] := by 
  norm_num [Int.ModEq]