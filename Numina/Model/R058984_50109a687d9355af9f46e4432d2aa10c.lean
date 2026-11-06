import Mathlib

theorem number_theory_7872 :
    IsLeast {x : ℕ | 0 < x ∧ x ≡ 1 [MOD 2] ∧ x ≡ 2 [MOD 3] ∧ x ≡ 3 [MOD 4] ∧ x ≡ 4 [MOD 5] ∧ x ≡ 5 [MOD 6] ∧ x ≡ 6 [MOD 7]} 419 := by
  constructor
  · -- Verify 419 is in the set.
    constructor
    · -- Show that 419 is greater than 0.
      norm_num
    constructor
    · -- Show that 419 ≡ 1 [MOD 2]
      norm_num [Nat.ModEq]
    constructor
    · -- Show that 419 ≡ 2 [MOD 3]
      norm_num [Nat.ModEq]
    constructor
    · -- Show that 419 ≡ 3 [MOD 4]
      norm_num [Nat.ModEq]
    constructor
    · -- Show that 419 ≡ 4 [MOD 5]
      norm_num [Nat.ModEq]
    constructor
    · -- Show that 419 ≡ 5 [MOD 6]
      norm_num [Nat.ModEq]
    · -- Show that 419 ≡ 6 [MOD 7]
      norm_num [Nat.ModEq]
  · -- Show that 419 is the smallest element in the set
    intro x hx
    rcases hx with ⟨hx_pos, hx_mod_2, hx_mod_3, hx_mod_4, hx_mod_5, hx_mod_6, hx_mod_7⟩
    by_contra h
    push_neg at h
    interval_cases x <;> norm_num [Nat.ModEq] at hx_mod_2 hx_mod_3 hx_mod_4 hx_mod_5 hx_mod_6 hx_mod_7 <;> omega