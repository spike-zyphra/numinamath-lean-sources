import Mathlib

theorem number_theory_229307 (n : ℕ) :
    Nat.Prime (2^n - 1) ∧ Nat.Prime (2^n + 1) ↔ n = 2 := by 
  constructor
  · -- Assume both $2^n - 1$ and $2^n + 1$ are prime, prove $n = 2$.
    intro h 
    rcases h with ⟨h1, h2⟩ 
    by_cases h3 : n > 2 
    · -- Assume n > 2.
      have h4 : n > 2 := h3 
      have h5 : n ≥ 3 := by omega 
      by_cases h6 : n % 2 = 1 
      · -- Assume n is odd.
        have h7 : (2 ^ n + 1) % 3 = 0 := by 
          have h8 : ∀ (k : ℕ), (2 : ℕ) ^ (2 * k + 1) % 3 = 2 := by 
            intro k 
            induction k with 
            | zero => 
              simp 
            | succ k ih => 
              simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢ 
              omega 
          have h9 : ∃ k, n = 2 * k + 1 := by 
            refine' ⟨(n - 1) / 2, by omega⟩ 
          rcases h9 with ⟨k, hk⟩ 
          rw [show n = 2 * k + 1 by omega] 
          have h10 : (2 ^ (2 * k + 1) + 1) % 3 = 0 := by 
            have h11 : (2 ^ (2 * k + 1) : ℕ) % 3 = 2 := h8 k 
            omega 
          omega 
        have h8 : ¬ Nat.Prime (2 ^ n + 1) := by 
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (2 ^ n + 1) by omega) 
          all_goals 
            have h9 : 2 ^ n > 3 := by 
              have h11 : n ≥ 3 := by omega 
              have h12 : 2 ^ n ≥ 2 ^ 3 := by 
                apply Nat.pow_le_pow_of_le_right (by norm_num) h11 
              norm_num at h12 ⊢ 
              omega 
            omega 
        contradiction 
      · -- Assume n is even.
        have h6' : n % 2 = 0 := by omega 
        have h8 : (2 ^ n - 1) % 3 = 0 := by 
          have h9 : ∀ (k : ℕ), (2 : ℕ) ^ (2 * k) % 3 = 1 := by 
            intro k 
            induction k with 
            | zero => 
              simp 
            | succ k ih => 
              simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢ 
              omega 
          have h10 : ∃ k, n = 2 * k := by 
            refine' ⟨n / 2, by omega⟩ 
          rcases h10 with ⟨k, hk⟩ 
          rw [show n = 2 * k by omega] 
          have h11 : (2 ^ (2 * k) - 1) % 3 = 0 := by 
            have h12 : (2 ^ (2 * k) : ℕ) % 3 = 1 := h9 k 
            omega 
          omega 
        have h9 : ¬ Nat.Prime (2^n - 1) := by 
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (2 ^ n - 1) by omega) 
          all_goals 
            have h9 : 2 ^ n > 4 := by 
              have h11 : n ≥ 3 := by omega 
              have h12 : 2 ^ n ≥ 2 ^ 3 := by 
                apply Nat.pow_le_pow_of_le_right (by norm_num) h11 
              norm_num at h12 ⊢ 
              omega 
            have h10 : 2 ^ n - 1 > 3 := by 
              omega 
            all_goals 
              omega 
        contradiction 
    · -- Assume n ≤ 2.
      have h5 : n ≤ 2 := by omega 
      interval_cases n <;> norm_num at h1 h2 <;> tauto 
  · -- Assume n = 2, prove both $2^n - 1$ and $2^n + 1$ are prime.
    intro h 
    rw [h] 
    constructor 
    · -- Show 3 is prime 
      norm_num 
    · -- Show 5 is prime 
      norm_num