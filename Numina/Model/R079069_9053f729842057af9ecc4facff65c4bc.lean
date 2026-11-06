import Mathlib

theorem number_theory_14750 :
    IsLeast {n | n ≥ 10000 ∧ n ≡ 5 [MOD 15]} 10010 := by
  constructor
  · constructor
    · norm_num -- Show that 10010 ≥ 10000
    · norm_num [Nat.ModEq] -- Show that 10010 ≡ 5 [MOD 15]
  · intro n hn
    rcases hn with ⟨hn1, hn2⟩
    norm_num [Nat.ModEq] at hn2
    omega