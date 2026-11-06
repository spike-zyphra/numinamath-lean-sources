import Mathlib

theorem number_theory_111087 (n : ℕ) (hn : 0 < n) :
    ¬ Nat.Prime (14^n + 19) := by
  have h1 : n > 0 := by linarith
  have h2 : n % 2 = 0 ∨ n % 2 = 1 := by 
    omega
  rcases h2 with (h | h)
  · -- Case n is even
    have h3 : (14 ^ n + 19) % 5 = 0 := by
      have h4 : n % 2 = 0 := h
      have h5 : ∀ k : ℕ, (14 ^ (2 * k) + 19) % 5 = 0 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [pow_add, pow_mul] at ih ⊢
          all_goals
            omega
      have h6 : ∃ k, n = 2 * k := by 
        refine' ⟨n / 2, by omega⟩
      rcases h6 with ⟨k, hk⟩
      rw [show n = 2 * k by linarith [hk]]
      have h7 := h5 k
      omega
    have h4 : ¬ Nat.Prime (14 ^ n + 19) := by
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (14 ^ n + 19) by omega)
      all_goals
        have h6 : 14 ^ n > 1 := by
          have h2 : n ≥ 1 := by omega
          have h3 : 14 ^ n ≥ 14 ^ 1 := by apply Nat.pow_le_pow_of_le_right (by norm_num) h2
          have h4 : 14 ^ 1 = 14 := by norm_num
          linarith [h3, h4]
        omega
    tauto
  · -- Case n is odd
    have h3 : (14 ^ n + 19) % 3 = 0 := by
      have h4 : n % 2 = 1 := h
      have h5 : ∀ k : ℕ, (14 ^ (2 * k + 1) + 19) % 3 = 0 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [pow_add, pow_mul] at ih ⊢
          all_goals 
            omega
      have h6 : ∃ k, n = 2 * k + 1 := by 
        refine' ⟨(n - 1) / 2, by omega⟩
      rcases h6 with ⟨k, hk⟩
      rw [show n = 2 * k + 1 by linarith [hk]]
      have h7 := h5 k
      omega
    have h4 : ¬ Nat.Prime (14 ^ n + 19) := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (14 ^ n + 19) by omega)
      all_goals
        have h6 : 14 ^ n > 1 := by
          have h2 : n ≥ 1 := by omega
          have h3 : 14 ^ n ≥ 14 ^ 1 := by apply Nat.pow_le_pow_of_le_right (by norm_num) h2
          have h4 : 14 ^ 1 = 14 := by norm_num
          linarith [h3, h4]
        omega
    tauto