import Mathlib

theorem number_theory_206310 :
    IsLeast {n : ℕ | n > 0 ∧ (∃ k, n = 2 * k ^ 2) ∧ (∃ m, n = 3 * m ^ 3)} 648 := by
  constructor
  · -- Show that 648 is in the set.
    constructor
    · norm_num
    constructor
    · -- Show that 648 = 2 * k^2 for some k
      use 18
      all_goals norm_num
    · -- Show that 648 = 3 * m^3 for some m
      use 6
      all_goals norm_num
  · -- Show that no integer less than 648 is in the set.
    intro n hn
    rcases hn with ⟨hn_pos, ⟨k, hk⟩, ⟨m, hm⟩⟩
    by_contra h
    push_neg at h
    have h1 : k ^ 2 * 2 = n := by
      linarith
    have h2 : m ^ 3 * 3 = n := by
      linarith
    have h3 : k ≤ 18 := by
      nlinarith
    have h4 : m ≤ 5 := by
      have h10 : m ^ 3 < 216 := by
        nlinarith [sq_nonneg (m : ℕ), sq_nonneg (k : ℕ), h]
      have h11 : m < 6 := by
        by_contra h12
        push_neg at h12
        have h13 : m ^ 3 ≥ 216 := by
          have : m ≥ 6 := by linarith
          have h14 : m ^ 3 ≥ 6 ^ 3 := by apply Nat.pow_le_pow_of_le_left; linarith
          nlinarith
        linarith
      omega
    interval_cases k <;> interval_cases m <;> omega