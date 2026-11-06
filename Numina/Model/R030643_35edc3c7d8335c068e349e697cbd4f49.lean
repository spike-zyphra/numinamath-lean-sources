import Mathlib

theorem number_theory_279953 (n : ℕ) :
    1961 ∣ 5^(2*n) * 3^(4*n) - 2^(6*n) := by
  have h1 : (5 ^ (2 * n) * 3 ^ (4 * n) : ℕ) = (2025 ^ n : ℕ) := by 
    have h4 : ∀ n : ℕ, (5 ^ (2 * n) * 3 ^ (4 * n) : ℕ) = (2025 ^ n : ℕ) := by
      intro n
      induction n with 
      | zero => 
        simp
      | succ n ih => 
        simp [pow_succ, pow_mul] at ih ⊢ 
        all_goals
          ring_nf at ih ⊢ 
          <;> omega 
    specialize h4 n 
    simpa using h4 
  have h2 : (2 ^ (6 * n) : ℕ) = (64 ^ n : ℕ) := by 
    have h4 : ∀ n : ℕ, (2 ^ (6 * n) : ℕ) = (64 ^ n : ℕ) := by 
      intro n 
      induction n with 
      | zero => 
        simp 
      | succ n ih => 
        simp [pow_succ, pow_mul] at ih ⊢ 
        all_goals 
          ring_nf at ih ⊢ 
          <;> omega 
    specialize h4 n 
    simpa using h4 
  rw [h1, h2] 
  have h3 : ∀ n : ℕ, 1961 ∣ (2025 ^ n : ℕ) - (64 ^ n : ℕ) := by
    intro n
    induction n with 
    | zero => 
      simp 
    | succ n ih => 
      have eq3 : (2025 ^ (n + 1) : ℕ) - (64 ^ (n + 1) : ℕ) = 2025 * (2025 ^ n) - 64 * (64 ^ n) := by 
        ring_nf 
        <;> omega 
      rw [eq3] at *
      -- Now, we need to prove that `1961 \mid 2025 \cdot (2025^n) - 64 \cdot (64^n)`.
      -- We can use the fact that `1961 = 61 * 32`.
      -- We can also use the induction hypothesis `ih : 1961 ∣ 2025^n - 64^n`.
      have eq4 : 1961 ∣ 2025 * (2025 ^ n) - 64 * (64 ^ n) := by 
        have h5 : (2025 * (2025 ^ n) : ℕ) % 1961 = (64 * (64 ^ n) : ℕ) % 1961 := by 
          have h31 : ∀ k : ℕ, (2025 ^ k : ℕ) % 1961 = (64 ^ k : ℕ) % 1961 := by 
            intro k 
            induction k with 
            | zero => 
              simp 
            | succ k ih_k => 
              simp [Nat.pow_succ, Nat.mul_mod] at ih_k ⊢ 
              all_goals 
                omega 
          specialize h31 n 
          have h8 : (2025 * (2025 ^ n) : ℕ) % 1961 = (64 * (64 ^ n) : ℕ) % 1961 := by 
            simp [Nat.mul_mod, h31] 
          exact h8 
        exact Nat.dvd_of_mod_eq_zero (show ((2025 * (2025 ^ n) - (64 * (64 ^ n))) : ℕ) % 1961 = 0 by 
          omega 
        )
      exact_mod_cast eq4
  specialize h3 n 
  exact h3