import Mathlib

theorem number_theory_110911 (a : ℕ → ℕ) (ha : (a 0 = 1) ∧ (a 1 = 3) ∧ (∀ n : ℕ, a (n + 2) = a (n + 1) * 2 + 1)) : IsSquare (a 2013 + 1) := by
  rcases ha with ⟨ha0, ha1, hah⟩
  have h1 : ∀ k : ℕ, IsSquare (a (2 * k + 1) + 1) := by
    intro k 
    have h2 : ∀ m : ℕ, IsSquare (a (2 * m + 1) + 1) := by 
      intro m 
      induction' m using Nat.strongRecOn with m ih
      cases m with
      | zero =>
        rw [show 2 * 0 + 1 = 1 by omega]
        rw [ha1]
        use 2 
        all_goals norm_num
      | succ m =>
        have h3 : a (2 * (m + 1) + 1) + 1 = 4 * (a (2 * m + 1) + 1) := by
          have h4 : a (2 * (m + 1) + 1) = a (2 * m + 3) := by 
            ring_nf 
          have h5 : a (2 * m + 3) = 4 * a (2 * m + 1) + 3 := by 
            have h6 : a (2 * m + 3) = a (2 * m + 2) * 2 + 1 := by 
              specialize hah (2 * m + 1)
              simpa using hah 
            have h7 : a (2 * m + 2) = a (2 * m + 1) * 2 + 1 := by 
              specialize hah (2 * m)
              simpa using hah 
            rw [h7] at h6 
            omega 
          have h8 : a (2 * m + 1) + 1 = a (2 * m + 1) + 1 := rfl 
          rw [h4, h5] 
          all_goals 
            omega 
        have h9 : IsSquare (a (2 * m + 1) + 1) := by 
          apply ih 
          all_goals 
            omega 
        rw [h3] 
        obtain ⟨x, hx⟩ := h9 
        use 2 * x 
        nlinarith [hx] 
    specialize h2 k 
    simpa using h2 
  have h2 : IsSquare (a 2013 + 1) := by 
    specialize h1 1006 
    have h3 : 2 * (1006 : ℕ) + 1 = 2013 := by omega 
    rw [show 2 * (1006 : ℕ) + 1 = 2013 by omega] at h1
    tauto 
  exact h2