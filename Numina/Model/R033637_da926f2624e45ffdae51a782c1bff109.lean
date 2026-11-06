import Mathlib

theorem number_theory_324794 (n : ℕ) :
    ∃ k, n^3 + 2*n^2 + 9*n + 8 = k^3 ↔ n = 7 := by

  use 8
  constructor
  · -- Assume n^3 + 2*n^2 + 9*n + 8 = 8^3, prove n = 7
    intro h
    have h1 : n ≤ 7 := by
      by_contra h2
      push_neg at h2
      have h2' : n ≥ 8 := by omega
      have h3 : n ^ 3 + 2 * n ^ 2 + 9 * n + 8 > 8 ^ 3 := by
        have h5 : n ≥ 8 := h2'
        have h6 : n ^ 3 + 2 * n ^ 2 + 9 * n + 8 > 8 ^ 3 := by
          have h7 : n ^ 3 ≥ 512 := by
            have h8 : n ≥ 8 := h5
            have h9 : n ^ 3 ≥ 8 ^ 3 := by
              apply Nat.pow_le_pow_of_le_left h8 3
            norm_num at h9 ⊢
            linarith
          have h8 : 2 * n ^ 2 ≥ 128 := by
            have h9 : n ≥ 8 := h5
            have h10 : n ^ 2 ≥ 64 := by
              nlinarith
            nlinarith
          have h9 : 9 * n ≥ 72 := by
            have h10 : n ≥ 8 := h5
            omega
          omega
        linarith
      have h4 : n ^ 3 + 2 * n ^ 2 + 9 * n + 8 = 8 ^ 3 := by
        linarith [h]
      have h11 : n ^ 3 + 2 * n ^ 2 + 9 * n + 8 > 8 ^ 3 := h3
      linarith [h4, h11]
    have h2 : n = 7 := by
      interval_cases n <;> omega
    exact h2
  · -- Assume n = 7, prove n^3 + 2*n^2 + 9*n + 8 = 8^3
    intro h
    rw [h]
    all_goals norm_num