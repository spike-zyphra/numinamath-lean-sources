import Mathlib

theorem number_theory_184335 : 2^9 + 2^99 ≡ 0 [ZMOD 100] := by 
  norm_num [Int.ModEq]