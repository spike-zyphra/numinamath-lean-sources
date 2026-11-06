import Mathlib

theorem number_theory_215637 (n : ℕ) (hn : 2 < n) :
    ¬(Nat.Prime (2^n - 1) ∧ Nat.Prime (2^n + 1)) := by 
  intro h
  rcases h with ⟨h1, h2⟩

  have h3 : n % 2 = 0 ∨ n % 2 = 1 := by 
    omega
  
  rcases h3 with (h3 | h3)
  · -- Assume n is even
    have h4 : (2 : Nat) ^ n % 3 = 1 := by
      have h6 : ∃ k : Nat, n = 2 * k := by 
        refine' ⟨n / 2, by omega⟩
      rcases h6 with ⟨k, hk⟩
      rw [show n = 2 * k by linarith]
      have h5 : ∀ k : Nat, (2 : Nat) ^ (2 * k) % 3 = 1 := by 
        intro k 
        induction k with 
        | zero => 
          norm_num 
        | succ k ih => 
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals omega 
      apply h5 k
    have h6 : ((2 : Nat) ^ n - 1) % 3 = 0 := by 
      have h8 : (2 : Nat) ^ n > 1 := by
        have : n > 0 := by linarith 
        have h7 : (2 : Nat) ^ n ≥ (2 : Nat) ^ 1 := by
          apply Nat.pow_le_pow_of_le_right 
          all_goals linarith 
        have h8 : (2 : Nat) ^ 1 = 2 := by norm_num 
        have : (2 : Nat) ^ n ≥ 2 := by linarith 
        omega 
      omega
    -- Show that $2^n - 1$ is not prime
    have h7 : ¬Nat.Prime ((2 : Nat) ^ n - 1) := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ ((2 : Nat) ^ n - 1) by omega) (by 
        have h8 : (2 : Nat) ^ n - 1 > 1 := by
          have : n > 2 := by linarith 
          have h9 : (2 : Nat) ^ n ≥ (2 : Nat) ^ 3 := by 
            apply Nat.pow_le_pow_of_le_right 
            all_goals linarith 
          have h8 : (2 : Nat) ^ 3 = 8 := by norm_num
          have : (2 : Nat) ^ n > 1 := by 
            omega 
          omega 
        omega 
      ) (by 
        have h8 : (2 : Nat) ^ n - 1 > 3 := by 
          have : n > 2 := by linarith 
          have h9 : (2 : Nat) ^ n ≥ (2 : Nat) ^ 3 := by 
            apply Nat.pow_le_pow_of_le_right 
            all_goals linarith 
          have h8 : (2 : Nat) ^ 3 = 8 := by norm_num 
          omega 
        omega 
      )
    contradiction
  · -- Assume n is odd
    have h4 : (2 : Nat) ^ n % 3 = 2 := by 
      have h6 : ∃ k : Nat, n = 2 * k + 1 := by 
        refine' ⟨(n - 1) / 2, by 
          omega 
        ⟩ 
      rcases h6 with ⟨k, hk⟩ 
      rw [show n = 2 * k + 1 by linarith] 
      have h5 : ∀ k : Nat, (2 : Nat) ^ (2 * k + 1) % 3 = 2 := by 
        intro k 
        induction k with 
        | zero => 
          norm_num 
        | succ k ih => 
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals omega 
      apply h5 k
    have h6 : ((2 : Nat) ^ n + 1) % 3 = 0 := by 
      omega
    -- Show that $2^n + 1$ is not prime
    have h7 : ¬Nat.Prime ((2 : Nat) ^ n + 1) := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ ((2 : Nat) ^ n + 1) by omega) (by 
        have h8 : (2 : Nat) ^ n + 1 > 1 := by 
          have : n > 0 := by linarith 
          have h7 : (2 : Nat) ^ n ≥ (2 : Nat) ^ 1 := by 
            apply Nat.pow_le_pow_of_le_right 
            all_goals linarith 
          have h8 : (2 : Nat) ^ 1 = 2 := by norm_num 
          have : (2 : Nat) ^ n ≥ 2 := by linarith 
          omega 
        omega 
      ) (by 
        have h8 : (2 : Nat) ^ n + 1 > 3 := by 
          have : n > 2 := by linarith 
          have h9 : (2 : Nat) ^ n ≥ (2 : Nat) ^ 3 := by 
            apply Nat.pow_le_pow_of_le_right 
            all_goals linarith 
          have h8 : (2 : Nat) ^ 3 = 8 := by norm_num 
          omega 
        omega 
      )
    contradiction