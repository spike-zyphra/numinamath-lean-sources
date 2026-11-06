import Mathlib

theorem number_theory_7111 : (2468)^2 ≡ 1024 [ZMOD 10000] := by 
  norm_num [Int.ModEq]