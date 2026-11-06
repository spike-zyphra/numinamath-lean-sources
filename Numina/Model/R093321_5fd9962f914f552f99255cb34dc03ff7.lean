import Mathlib

theorem number_theory_134005 : (3^(8^7)) ≡ 1 [MOD 10] := by
  norm_num [Nat.ModEq]