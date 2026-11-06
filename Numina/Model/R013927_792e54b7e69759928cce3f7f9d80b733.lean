import Mathlib
open Nat

theorem number_theory_160891 (n k : ℕ) (h₀ : 0 < n) (h₁ : 0 < k)
    (h₂ : (n ! : ℕ) + 3 * n + 8 = k ^ 2) :
    n = 2 ∧ k = 4 := by
  by_cases h : n < 3
  · -- n < 3, so n = 1 or 2
    interval_cases n <;> try { 
      -- check n = 1 and n = 2
      norm_num [Nat.factorial] at h₂
      all_goals
        have h4 : k ≤ 7 := by nlinarith
        interval_cases k <;> omega
    }
  · -- n ≥ 3
    have h3 : n ≥ 3 := by omega
    have h4 : (3 : ℕ) ∣ (n !) := by
      apply Nat.dvd_factorial
      all_goals linarith
    have h5 : (n ! : ℕ) % 3 = 0 := by 
      exact Nat.dvd_iff_mod_eq_zero.mp h4
    have h6 : (k ^ 2) % 3 = 0 ∨ (k ^ 2) % 3 = 1 := by 
      have h1 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by 
        omega
      rcases h1 with (h1 | h1 | h1)
      · -- k ≡ 0
        simp [Nat.pow_mod, h1]
      · -- k ≡ 1
        simp [Nat.pow_mod, h1]
      · -- k ≡ 2
        simp [Nat.pow_mod, h1]
    have h7 : ((n ! : ℕ) + 3 * n + 8) % 3 = 2 := by 
      have h8 : (n ! : ℕ) % 3 = 0 := h5
      have h9 : (3 * n) % 3 = 0 := by 
        simp [Nat.mul_mod]
      omega
    have h8 : (k ^ 2) % 3 = 2 := by 
      omega
    omega