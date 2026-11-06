import Mathlib

theorem number_theory_198732 (n : ℕ) :
    IsSquare (2^n + 5) ↔ n = 2 := by
  constructor
  · -- Assume that 2^n + 5 is a perfect square, prove that n = 2.
    intro h
    rcases h with ⟨k, hk⟩
    by_cases h1 : n ≤ 2
    · -- If n ≤ 2, then compute 2^n + 5.
      interval_cases n <;> try { 
        all_goals 
          try { 
            have : k ≤ 5 := by nlinarith 
            interval_cases k <;> try { 
              all_goals 
                omega 
            }
          }
      }
    · -- n > 2
      have h2 : n > 2 := by omega 
      have h3 : k ^ 2 = 2 ^ n + 5 := by
        nlinarith
      have h4 : k ^ 2 % 8 = 0 ∨ k ^ 2 % 8 = 1 ∨ k ^ 2 % 8 = 4 := by
        have h1 : k % 8 = 0 ∨ k % 8 = 1 ∨ k % 8 = 2 ∨ k % 8 = 3 ∨ k % 8 = 4 ∨ k % 8 = 5 ∨ k % 8 = 6 ∨ k % 8 = 7 := by 
          omega
        rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> norm_num [Nat.pow_mod, h1, Nat.mul_mod]
      have h5 : (2 : ℕ) ^ n % 8 = 0 := by
        have h6 : ∀ m : ℕ, (2 : ℕ) ^ (m + 3) % 8 = 0 := by
          intro m
          induction m with
          | zero => 
            norm_num
          | succ m ih =>
            simp [Nat.pow_add, Nat.mul_mod, show (2 : ℕ) ^ 3 = 8 from by norm_num] at ih ⊢
            <;> omega
        have h7 : n ≥ 3 := by omega
        have h8 : ∃ m : ℕ, n = m + 3 := by
          refine' ⟨n - 3, by omega⟩
        rcases h8 with ⟨m, hm⟩
        rw [show n = m + 3 by omega]
        exact h6 m
      have h7 : (2 ^ n + 5 : ℕ) % 8 = 5 := by
        have h8 : (2 ^ n : ℕ) % 8 = 0 := h5
        omega
      have h8 : k ^ 2 % 8 = 5 := by
        omega
      omega
  · -- Assume n = 2, prove that 2^n + 5 is a perfect square.
    intro h
    rw [h]
    native_decide