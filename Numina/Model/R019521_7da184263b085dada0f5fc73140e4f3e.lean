import Mathlib

theorem number_theory_15553 :
    IsLeast {n : ℕ | 0 < n ∧ ∃ k, 3 * n = k ^ 2 ∧ ∃ m, 2 * n = m ^ 3} 108 := by
  constructor
  · -- Show that 108 is indeed in the set
    constructor
    · norm_num
    use 18
    constructor
    · norm_num
    use 6
    all_goals norm_num
  · -- Show that 108 is the smallest
    intro n hn
    rcases hn with ⟨hn_pos, k, hk, m, hm⟩
    by_contra h
    push_neg at h
    have h1 : k < 18 := by
      nlinarith [hk, h, show 0 < n from by linarith]
    have h2 : m < 6 := by
      have h3 : m ^ 3 < (6 : ℕ) ^ 3 := by
        nlinarith [hm, h, show 0 < n from by linarith]
      have : m < (6 : ℕ) := by
        by_contra h4
        push_neg at h4
        have h5 : m ^ 3 ≥ (6 : ℕ) ^ 3 := by
          have : m ≥ 6 := by linarith
          have h6 : m ^ 3 ≥ (6 : ℕ) ^ 3 := by
            apply Nat.pow_le_pow_of_le_left
            linarith
          linarith
        linarith
      linarith
    interval_cases m <;> try { 
      interval_cases k <;> all_goals
        omega
    }