import Mathlib

theorem number_theory_5064 : 29^((2022):ℕ) ≡ 1 [MOD 13] := by
  norm_num [Nat.ModEq]