import Mathlib

theorem number_theory_15191 : 73 * 73 ≡ 1 [MOD 74] := by
  norm_num [Nat.ModEq]