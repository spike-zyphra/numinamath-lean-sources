import Mathlib

theorem number_theory_7204 (k : ℕ) : 19 ∣ (2^(2^ (6 * k + 2)) + 3) := by

  have h1 : ∀ k : ℕ, (2 ^ (2 ^ (6 * k + 2)) : ℕ) % 19 = 16 := by 
    intro k 
    have h3 : ∀ (k : ℕ), (2 ^ (2 ^ (6 * k + 2)) : ℕ) % 19 = 16 := by
      intro k 
      induction k with 
      | zero =>
        norm_num
      | succ k ih =>
        have h4 : (2 ^ (2 ^ (6 * (k + 1) + 2)) : ℕ) % 19 = 16 := by 
          have h5 : (2 ^ (2 ^ (6 * (k + 1) + 2)) : ℕ) = (2 ^ (2 ^ (6 * k + 2)) ) ^ 64 := by 
            ring_nf 
          rw [h5] 
          have h7 : ((2 ^ (2 ^ (6 * k + 2)) : ℕ) ) % 19 = 16 := ih 
          have h8 : ((2 ^ (2 ^ (6 * k + 2)) ) ^ 64 : ℕ) % 19 = 16 := by 
            simp [Nat.pow_mod, h7] 
          exact h8 
        exact h4 
    specialize h3 k 
    simpa using h3 
  have h1_k : (2 ^ (2 ^ (6 * k + 2)) : ℕ) % 19 = 16 := h1 k 
  omega