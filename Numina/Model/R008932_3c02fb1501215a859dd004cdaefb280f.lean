import Mathlib

theorem number_theory_15850 (_ : Nat.ModEq 47 (13 * 29) 1) : 34 * 18 ≡ 1 [MOD 47] := by
  norm_num [Nat.ModEq]