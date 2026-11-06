import Mathlib

theorem number_theory_6376 : IsLeast {n : ℕ | 0 < n ∧ n % 9 = 7 ∧ n % 10 = 8 ∧ n % 11 = 9} 988 := by
  constructor
  · constructor
    · norm_num  -- Show 988 > 0
    constructor
    · norm_num  -- Show 988 % 9 = 7
    constructor
    · norm_num  -- Show 988 % 10 = 8
    · norm_num  -- Show 988 % 11 = 9
  · intro n hn
    rcases hn with ⟨hn_pos, hn_mod_9, hn_mod_10, hn_mod_11⟩
    omega