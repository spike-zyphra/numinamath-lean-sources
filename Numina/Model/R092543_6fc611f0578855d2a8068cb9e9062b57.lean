import Mathlib

theorem number_theory_111803 : 5^120 + 2^150 ≡ 0 [ZMOD 13] := by
  norm_num [Int.ModEq]