import Mathlib

theorem number_theory_7873 (n : ℕ) (hn : n > 0) :
    Nat.Prime (n ^ n + 1) ∧ (n ^ n + 1) ≤ 10 ^ 19 ↔ n ^ n + 1 = 2 ∨ n ^ n + 1 = 5 ∨ n ^ n + 1 = 257 := by
  constructor
  · -- Forward direction: If $n^n +1$ is prime and ≤ 10^19, then it is one of 2, 5, 257
    intro h
    rcases h with ⟨h_prime, h_le⟩
    have h1 : n ≤ 19 := by
      by_contra h2
      push_neg at h2
      have h2 : n ≥ 20 := by
        omega
      have h3 : n ^ n ≥ 20 ^ 20 := by
        have h4 : n ≥ 20 := h2
        have h5 : n ^ n ≥ n ^ 20 := by
          have : n ≥ 20 := h4
          have : n ^ 20 ≤ n ^ n := by
            apply Nat.pow_le_pow_of_le_right
            all_goals
              omega
          linarith
        have h6 : n ^ 20 ≥ 20 ^ 20 := by
          apply Nat.pow_le_pow_of_le_left
          all_goals
            omega
        have h7 : n ^ n ≥ 20 ^ 20 := by
          linarith [h5, h6]
        linarith
      have h4 : n ^ n + 1 > 10 ^ 19 := by
        have h5 : n ^ n ≥ 20 ^ 20 := h3
        have h6 : n ^ n + 1 ≥ 20 ^ 20 + 1 := by
          linarith
        norm_num at h6 ⊢
        linarith
      linarith
    interval_cases n <;> norm_num at h_prime h_le ⊢ <;> try { tauto }
  · -- Backward direction: If it is 2, 5, 257, then it is prime and ≤ 10^19
    rintro (h | h | h)
    · -- Case where n^n + 1 = 2
      rw [h]
      constructor
      · norm_num
      all_goals norm_num
    · -- Case where n^n + 1 = 5
      rw [h]
      constructor
      · norm_num
      all_goals norm_num
    · -- Case where n^n + 1 = 257
      rw [h]
      constructor
      · norm_num
      all_goals norm_num