import Mathlib

theorem number_theory_12314 :
    IsLeast {m : ℕ | ∃ n : ℕ, 0 < m ∧ 0 < n ∧ 24 * m = n ^ 4} 54 := by
  constructor
  · -- Show that 54 is in the set with n = 6
    use 6
    all_goals norm_num
  · -- Show that 54 is minimal
    intro k hk
    rcases hk with ⟨n, hn1, hn2, h_eq⟩
    by_contra h
    push_neg at h
    have h1 : n ≤ 5 := by
      by_contra h2
      push_neg at h2
      have h3 : n ^ 4 ≥ 6 ^ 4 := by
        have h4 : n ≥ 6 := by linarith
        have h5 : n ^ 4 ≥ 6 ^ 4 := by
          apply Nat.pow_le_pow_of_le_left
          exact h4
          all_goals linarith
        linarith
      have h4 : 24 * k ≥ 6 ^ 4 := by
        nlinarith [h_eq, h3]
      have h5 : k ≥ 54 := by
        nlinarith
      linarith
    have : n ≤ 5 := by linarith
    interval_cases n <;> omega