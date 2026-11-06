import Mathlib

theorem number_theory_4689_1 : 4 * 13 ≡ 1 [MOD 17] := by decide

theorem number_theory_4689_2 : 5 * 7 ≡ 1 [MOD 17] := by decide

theorem number_theory_4689_3 : 7 * 5 ≡ 1 [MOD 17] := by decide

theorem number_theory_4689_4 : 16 * 16 ≡ 1 [MOD 17] := by
  norm_num [Nat.ModEq]