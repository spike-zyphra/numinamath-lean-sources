import Mathlib

theorem number_theory_15379 : 11 * 91 ≡ 1 [ZMOD 1000] := by
  norm_num [Int.ModEq]