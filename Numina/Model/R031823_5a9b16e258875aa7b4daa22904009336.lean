import Mathlib

theorem exists_minval : (∃ (a b c : ℕ),
  a^b * b^c = a^c ∧ 
  0 < a ∧ 0 < b ∧ 0 < c ∧ 
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ 
  a + b + c = 13) ∧ ∀ (a b c : ℕ), a^b * b^c = a^c ∧ 
  0 < a ∧ 0 < b ∧ 0 < c ∧ 
  a ≠ b ∧ b ≠ c ∧ a ≠ c → a + b + c ≥ 13 := by

  constructor
  · -- Show that (8, 2, 3) is a valid solution.
    use 8, 2, 3
    constructor
    · -- Show 8^2 * 2^3 = 8^3
      norm_num
    constructor
    · -- Show 0 < 8
      norm_num
    constructor
    · -- Show 0 < 2
      norm_num
    constructor
    · -- Show 0 < 3
      norm_num
    constructor
    · -- Show 8 ≠ 2
      norm_num
    constructor
    · -- Show 2 ≠ 3
      norm_num
    constructor
    · -- Show 8 ≠ 3
      norm_num
    · -- Show 8 + 2 + 3 = 13
      norm_num
  · -- Show that any solution must have a + b + c ≥ 13
    intro a b c h
    rcases h with ⟨h_eq, ha, hb, hc, hab, hbc, hac⟩
    by_contra h
    push_neg at h
    have h1 : a + b + c < 13 := by linarith
    have h2 : a ≤ 9 := by
      omega
    have h3 : b ≤ 9 := by
      omega
    have h4 : c ≤ 9 := by
      omega
    interval_cases a <;> interval_cases b <;> interval_cases c
    all_goals
      norm_num at h_eq ⊢
      all_goals
        omega