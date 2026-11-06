import Mathlib

open Nat

theorem number_theory_1653 (n : ℕ) (h₀ : Nat.Prime n) (h₁ : Nat.Prime (n + 6)) (h₂ : Nat.Prime (n + 8)) (h₃ : Nat.Prime (n + 12)) (h₄ : Nat.Prime (n + 14)) : n = 5 := by
  by_cases hn : n ≤ 20
  · interval_cases n <;> norm_num [Nat.prime_iff, Nat.succ_pos'] at h₀ h₁ h₂ h₃ h₄ ⊢ <;> tauto
  · -- n > 20
    have h5 : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      by_contra h
      push_neg at h
      have : n % 5 = 0 := by
        omega
      have : ¬ Nat.Prime n := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ n by omega)
        all_goals omega
      contradiction
    rcases h5 with (h5 | h5 | h5 | h5)
    · -- n % 5 = 1
      have h0 : (n + 14) % 5 = 0 := by
        omega
      have h6 : ¬ Nat.Prime (n + 14) := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (n + 14) by omega)
        all_goals omega
      contradiction
    · -- n % 5 = 2
      have h0 : (n + 8) % 5 = 0 := by
        omega
      have h6 : ¬ Nat.Prime (n + 8) := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (n + 8) by omega)
        all_goals omega
      contradiction
    · -- n % 5 = 3
      have h0 : (n + 12) % 5 = 0 := by
        omega
      have h6 : ¬ Nat.Prime (n + 12) := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (n + 12) by omega)
        all_goals omega
      contradiction
    · -- n % 5 = 4
      have h0 : (n + 6) % 5 = 0 := by
        omega
      have h6 : ¬ Nat.Prime (n + 6) := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (n + 6) by omega)
        all_goals omega
      contradiction