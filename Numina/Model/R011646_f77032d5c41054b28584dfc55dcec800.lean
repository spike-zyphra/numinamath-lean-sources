import Mathlib

theorem number_theory_266978 (p : ℕ) (hp : p.Prime) :
    p % 30 = 1 ∨ (p % 30).Prime := by
  by_cases h : p ≤ 30
  · interval_cases p <;> norm_num at hp ⊢ <;> tauto
  · -- p > 30
    have h1 : p % 2 = 1 := by
      by_contra h'
      have : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by norm_num) (by nlinarith)
      contradiction
    have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
      have hne : p % 3 ≠ 0 := by
        by_contra h'
        have : 3 ∣ p := by
          omega
        have : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by norm_num) (by nlinarith)
        contradiction
      omega
    have h3 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
      have hne : p % 5 ≠ 0 := by
        by_contra h'
        have : 5 ∣ p := by
          omega
        have : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega) (by norm_num) (by nlinarith)
        contradiction
      omega
    have h4 : p % 30 = 1 ∨ p % 30 = 7 ∨ p % 30 = 11 ∨ p % 30 = 13 ∨ p % 30 = 17 ∨ p % 30 = 19 ∨ p % 30 = 23 ∨ p % 30 = 29 := by
      omega
    rcases h4 with (h | h | h | h | h | h | h | h)
    · -- Case p % 30 = 1
      left
      omega
    · -- Case p % 30 = 7
      right
      rw [h]
      norm_num
    · -- Case p % 30 = 11
      right
      rw [h]
      norm_num
    · -- Case p % 30 = 13
      right
      rw [h]
      norm_num
    · -- Case p % 30 = 17
      right
      rw [h]
      norm_num
    · -- Case p % 30 = 19
      right
      rw [h]
      norm_num
    · -- Case p % 30 = 23
      right
      rw [h]
      norm_num
    · -- Case p % 30 = 29
      right
      rw [h]
      norm_num