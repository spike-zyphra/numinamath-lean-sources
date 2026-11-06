import Mathlib

theorem number_theory_610865 : 17^103 + 5 ≡ 8 [MOD 10] := by
  norm_num [Nat.ModEq]