import Mathlib

theorem number_theory_16177 : IsLeast {n | 0 < n ∧ 3 * n ≡ 1356 [MOD 22]} 12 := by 
  constructor
  · -- Show that 12 is in the set, i.e., 0 < 12 and 3 * 12 ≡ 1356 [MOD 22]
    constructor
    · norm_num
    · norm_num [Nat.ModEq]
  · -- Assume n is in the set, we need to show n ≥ 12
    intro n hn
    rcases hn with ⟨hn_pos, hn_mod⟩
    norm_num [Nat.ModEq] at hn_mod
    omega