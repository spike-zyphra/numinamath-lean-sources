import Mathlib

theorem number_theory_128901 : 17^17 ≡ 7 [MOD 10] := by
  norm_num [Nat.ModEq]