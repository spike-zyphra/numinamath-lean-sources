import Mathlib

theorem number_theory_163514 (n : ℕ) (hn : 1 ≤ n) : 35 ∣ 3^(6*n) - 2^(6*n) := by
  have h1 : ∀ (n : ℕ), 35 ∣ 3 ^ (6 * n) - 2 ^ (6 * n) := by 
    intro n
    have h2 : ∀ (n : ℕ), (3 ^ (6 * n) : ℕ) % 35 = (2 ^ (6 * n) : ℕ) % 35 := by
      intro n
      induction n with
      | zero => 
        simp
      | succ n ih =>
        have h11 : (3 : ℕ) ^ (6 * (n + 1)) % 35 = (2 : ℕ) ^ (6 * (n + 1)) % 35 := by
          have h31 : (3 : ℕ) ^ (6 * (n + 1)) = (3 ^ (6 * n)) * (3 ^ 6) := by
            ring_nf
          have h32 : (2 : ℕ) ^ (6 * (n + 1)) = (2 ^ (6 * n)) * (2 ^ 6) := by
            ring_nf
          rw [h31, h32]
          simp [Nat.mul_mod, show (3 ^ 6 : ℕ) % 35 = 29 by norm_num, 
            show (2 ^ 6 : ℕ) % 35 = 29 by norm_num] at ih ⊢
          all_goals
            omega
        exact h11
    have h4 : (3 ^ (6 * n) : ℕ) % 35 = (2 ^ (6 * n) : ℕ) % 35 := h2 n
    have h5 : 35 ∣ (3 ^ (6 * n) - 2 ^ (6 * n) : ℕ) := by 
      omega
    exact h5
  specialize h1 n
  simpa using h1