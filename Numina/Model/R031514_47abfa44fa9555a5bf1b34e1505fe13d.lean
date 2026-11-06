import Mathlib

theorem number_theory_114235 (k : ℕ) :
    IsSquare (2 ^ k + 8 * k + 5) ↔ k = 2 := by
  constructor
  · -- Forward direction: If $2^k + 8k + 5$ is a perfect square, then $k = 2$.
    intro h
    rcases h with ⟨m, hm⟩
    have h1 : m ^ 2 = 2 ^ k + 8 * k + 5 := by
      linarith
    by_cases h2 : k < 3
    · -- k < 3, so k = 0, 1, or 2
      interval_cases k <;> try { 
        norm_num at hm h1 ⊢
        <;> try { 
          have : m ≤ 7 := by nlinarith 
          interval_cases m <;> omega 
        }
      }
    · -- k ≥ 3
      have h2 : k >= 3 := by linarith
      have h4 : (2 : ℕ) ^ k % 8 = 0 := by 
        have h4 : ∀ (k : ℕ), k ≥ 3 → (2 : ℕ) ^ k % 8 = 0 := by
          intro k hk
          have h1 : k ≥ 3 := hk
          have h2 : (2 : ℕ) ^ k % 8 = 0 := by
            have h3 : ∀ (n : ℕ), (2 : ℕ) ^ (n + 3) % 8 = 0 := by
              intro n
              induction n with
              | zero =>
                norm_num 
              | succ n ih =>
                simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
                all_goals omega
            specialize h3 (k - 3)
            have h4 : k - 3 + 3 = k := by
              omega
            rw [h4] at h3 
            omega 
          exact h2
        specialize h4 k h2 
        exact h4
      have eq1 : (2 ^ k + 8 * k + 5) % 8 = 5 := by 
        omega 
      have eq2 : m ^ 2 % 8 = 0 ∨ m ^ 2 % 8 = 1 ∨ m ^ 2 % 8 = 4 := by
        have h1 : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by
          omega 
        rcases h1 with (h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h, Nat.mul_mod, Nat.add_mod]
      have eq3 : m ^ 2 % 8 = 5 := by
        have h4 : m ^ 2 = 2 ^ k + 8 * k + 5 := by 
          linarith 
        omega 
      rcases eq2 with (h | h | h) 
      all_goals omega 
  · -- Backward direction: If $k = 2$, then $2^k + 8k + 5$ is a perfect square.
    intro h 
    rw [h] 
    use 5 
    all_goals norm_num