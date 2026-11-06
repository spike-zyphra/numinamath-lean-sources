import Mathlib

theorem number_theory_14477 :
    IsLeast {n : ℕ | 0 < n ∧ ∃ k, k^2 = 2 * n ∧ ∃ m, m^3 = 3 * n} 72 := by
  constructor
  · -- Show that 72 is in the set
    constructor
    · norm_num
    use 12
    constructor
    · norm_num
    use 6
    all_goals norm_num
  · -- Show that 72 is the least
    intro n hn
    rcases hn with ⟨hn_pos, k, hk, m, hm⟩
    by_contra h
    push_neg at h
    -- 2 * n < 144, so k < 12
    have h1 : k < 13 := by
      nlinarith [show k ^ 2 < (144 : ℕ) by nlinarith]
    -- 3 * n < 216, so m < 6
    have h2 : m < 7 := by
      have h3n : m ^ 3 < 216 := by
        nlinarith
      by_contra h
      push_neg at h
      have h3 : m ^ 3 ≥ 343 := by
        have h1 : m ≥ 7 := by linarith
        have h2 : m ^ 3 ≥ 7 ^ 3 := by
          apply Nat.pow_le_pow_of_le_left h1 3
        nlinarith
      nlinarith
    interval_cases k <;> interval_cases m
    all_goals
      omega