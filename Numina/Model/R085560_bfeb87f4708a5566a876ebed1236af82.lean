import Mathlib

theorem number_theory_158868 : IsLeast {n | n ≡ 1 [MOD 2] ∧ n ≡ 1 [MOD 3] ∧ n ≡ 1 [MOD 5] ∧ n ≡ 0 [MOD 7] ∧ n ≡ 1 [MOD 11]} 1981 := by
  constructor
  · -- Show that 1981 is in the set
    constructor
    · -- Show 1981 ≡ 1 [MOD 2]
      norm_num [Nat.ModEq]
    constructor
    · -- Show 1981 ≡ 1 [MOD 3]
      norm_num [Nat.ModEq]
    constructor
    · -- Show 1981 ≡ 1 [MOD 5]
      norm_num [Nat.ModEq]
    constructor
    · -- Show 1981 ≡ 0 [MOD 7]
      norm_num [Nat.ModEq]
    · -- Show 1981 ≡ 1 [MOD 11]
      norm_num [Nat.ModEq]
  · -- Show that 1981 is the smallest
    intro n hn
    rcases hn with ⟨h2, h3, h5, h7, h11⟩
    by_contra h
    push_neg at h
    have h8 : n < 1981 := h
    interval_cases n <;> norm_num [Nat.ModEq] at h2 h3 h5 h7 h11
    <;> all_goals omega