import Mathlib

open Nat

def is_prime (n : ℕ) := Nat.Prime n

theorem number_theory_195715 :
    ∀ n, is_prime n → n % 30 = 1 ∨ is_prime (n % 30) := by
  intro n h
  have h1 : Nat.Prime n := h
  by_cases h2 : n ≤ 30
  · interval_cases n <;> norm_num [is_prime] at h1 ⊢ <;> try { tauto }
  · -- Case `n > 30`
    have h3 : n > 30 := by linarith
    have h4 : n % 2 = 1 := by
      by_contra h'
      have h' : n % 2 = 0 := by omega
      have : n % 2 = 0 := by omega
      have h5 : ¬ Nat.Prime n := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ n by omega) (by linarith) (by linarith)
      contradiction
    have h5 : n % 3 = 1 ∨ n % 3 = 2 := by
      have h6 : n % 3 = 1 ∨ n % 3 = 2 ∨ n % 3 = 0 := by
        omega
      by_contra h
      push_neg at h
      have h7 : n % 3 = 0 := by
        omega
      have h8 : n % 3 = 0 := by
        omega
      have h9 : ¬ Nat.Prime n := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ n by omega) (by linarith) (by linarith)
      contradiction
    have h6 : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      have h7 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
        omega
      by_contra h
      push_neg at h
      have h8 : n % 5 = 0 := by
        omega
      have h9 : n % 5 = 0 := by
        omega
      have h10 : ¬ Nat.Prime n := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ n by omega) (by linarith) (by linarith)
      contradiction
    have h7 : n % 30 = 1 ∨ n % 30 = 7 ∨ n % 30 = 11 ∨ n % 30 = 13 ∨
        n % 30 = 17 ∨ n % 30 = 19 ∨ n % 30 = 23 ∨ n % 30 = 29 := by
      omega
    rcases h7 with (h | h | h | h | h | h | h | h)
    · -- Case `n % 30 = 1`
      omega
    · -- Case `n % 30 = 7`
      rw [h]
      norm_num [is_prime]
    · -- Case `n % 30 = 11`
      rw [h]
      norm_num [is_prime]
    · -- Case `n % 30 = 13`
      rw [h]
      norm_num [is_prime]
    · -- Case `n % 30 = 17`
      rw [h]
      norm_num [is_prime]
    · -- Case `n % 30 = 19`
      rw [h]
      norm_num [is_prime]
    · -- Case `n % 30 = 23`
      rw [h]
      norm_num [is_prime]
    · -- Case `n % 30 = 29`
      rw [h]
      norm_num [is_prime]