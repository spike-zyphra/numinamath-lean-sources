import Mathlib

theorem number_theory_276025 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Even (b^a - b) := by 
  have h1 : b ^ a % 2 = b % 2 := by 
    have h2 : b % 2 = 0 ∨ b % 2 = 1 := by 
      omega 
    rcases h2 with (h2 | h2)
    · 
      have h3 : b % 2 = 0 := h2
      have h4 : b ^ a % 2 = 0 := by
        have h5 : ∀ (k : ℕ), (b ^ (k + 1) : ℕ) % 2 = 0 := by 
          intro k
          induction k with
          | zero =>
            simp [h3, Nat.pow_mod]
          | succ k ih =>
            simp [Nat.pow_succ, Nat.mul_mod, h3] at ih ⊢
            all_goals omega 
        have ha1 : a ≥ 1 := by 
          omega 
        have h7 : a - 1 + 1 = a := by 
          omega 
        have h8 : (b ^ a) % 2 = 0 := by 
          have h9 : (b ^ (a - 1 + 1)) % 2 = 0 := h5 (a - 1)
          rw [show (a - 1 + 1 : ℕ) = a by omega] at h9 
          omega 
        omega 
      omega 
    · 
      have h4 : b % 2 = 1 := h2
      have h5 : b ^ a % 2 = 1 := by
        have h5' : ∀ (k : ℕ), (b ^ (k + 1) : ℕ) % 2 = 1 := by 
          intro k
          induction k with
          | zero =>
            simp [h4, Nat.pow_mod]
          | succ k ih =>
            simp [Nat.pow_succ, Nat.mul_mod, h4] at ih ⊢
            all_goals omega 
        have ha1 : a ≥ 1 := by 
          omega 
        have h7 : a - 1 + 1 = a := by 
          omega 
        have h8 : (b ^ a) % 2 = 1 := by 
          have h9 : (b ^ (a - 1 + 1)) % 2 = 1 := h5' (a - 1)
          rw [show (a - 1 + 1 : ℕ) = a by omega] at h9 
          omega 
        omega 
      omega 
  have h2 : (b ^ a - b) % 2 = 0 := by
    have h3 : b ≤ b ^ a := by 
      have ha1 : a ≥ 1 := by 
        omega 
      have h4 : b ^ 1 ≤ b ^ a := by 
        apply Nat.pow_le_pow_of_le_right 
        all_goals 
          omega 
      have h5 : b ^ 1 = b := by 
        ring 
      linarith 
    omega 
  exact ⟨(b ^ a - b) / 2, by omega⟩