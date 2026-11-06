import Mathlib

theorem number_theory_119160 : ∀ N : ℕ, ∃ n : ℕ, n > N ∧ ¬Nat.Prime (10 ^ n + 3) := by
  intro N
  use 6 * (N + 1) + 4
  constructor
  · -- Show that $6 * (N + 1) + 4 > N$ 
    omega 
  · -- Show that $10 ^ {n} + 3$ is composite
    have h2 : ¬ Nat.Prime (10 ^ (6 * (N + 1) + 4) + 3) := by
      have h3 : (10 ^ (6 * (N + 1) + 4) + 3) % 7 = 0 := by
        have h4 : ∀ (k : ℕ), (10 ^ (6 * k + 4) + 3) % 7 = 0 := by
          intro k 
          induction k with 
          | zero => 
            norm_num 
          | succ k ih => 
            have h5 : (10 : ℕ) ^ (6 * (k + 1) + 4) = (10 ^ (6 * k + 4)) * (10 ^ 6) := by 
              ring_nf 
            rw [h5] 
            norm_num at ih ⊢ 
            all_goals 
              try { omega } 
              <;> try { tauto }
        specialize h4 (N + 1) 
        norm_num at h4 ⊢ 
        all_goals try { omega } 
        all_goals try { tauto } 
      have h4 : ¬ Nat.Prime (10 ^ (6 * (N + 1) + 4) + 3) := by 
        apply Nat.not_prime_of_dvd_of_lt (show 7 ∣ (10 ^ (6 * (N + 1) + 4) + 3) by omega)
        all_goals 
          have h5 : 7 < 10 ^ (6 * (N + 1) + 4) + 3 := by 
            have h6 : 10 ^ (6 * (N + 1) + 4) ≥ 10 ^ 1 := by 
              have h7 : 6 * (N + 1) + 4 ≥ 1 := by 
                omega 
              have h8 : 10 ^ (6 * (N + 1) + 4) ≥ 10 ^ 1 := by 
                apply Nat.pow_le_pow_of_le_right (by linarith) h7 
              exact h8 
            omega 
          all_goals try { linarith } 
      exact h4 
    exact h2