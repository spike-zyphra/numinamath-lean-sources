import Mathlib

theorem number_theory_88344 : 2^147 - 1 ≡ 0 [ZMOD 343] := by
  norm_num [Int.ModEq]