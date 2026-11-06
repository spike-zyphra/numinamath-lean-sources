import Mathlib

theorem number_theory_4851 : 333^6 ≡ 666 [ZMOD 777] := by
  norm_num [Int.ModEq]