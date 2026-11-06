import Mathlib

theorem number_theory_158396 (p : ℕ) (hp : Nat.Prime p) :
    p % 24 = 1 ∨ ∃ q : ℕ, Nat.Prime q ∧ p % 24 = q := by
  by_cases h : p ≤ 24
  · -- p ≤ 24
    interval_cases p <;> norm_num at hp ⊢
    <;> try { tauto }
    <;> try { 
      use (p % 24)
      all_goals
        norm_num
    }
  · -- p > 24
    have h1 : p > 24 := by
      by_contra h'
      push_neg at h'
      have : p ≤ 24 := by omega
      linarith
    have h2 : p % 2 = 1 := by 
      by_contra h
      push_neg at h
      have : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
        all_goals omega
      contradiction
    have h3 : p % 3 = 1 ∨ p % 3 = 2 := by 
      by_contra h
      push_neg at h
      have : p % 3 = 0 := by omega
      have : 3 ∣ p := by 
        omega
      have : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega
      contradiction
    have : p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 ∨ p % 24 = 13 ∨ p % 24 = 17 ∨ p % 24 = 19 ∨ p % 24 = 23 := by
      omega
    rcases this with (h | h | h | h | h | h | h | h)
    · -- Case p % 24 = 1
      tauto
    · -- Case p % 24 = 5
      right
      use 5
      all_goals
        norm_num [h]
    · -- Case p % 24 = 7
      right
      use 7
      all_goals
        norm_num [h]
    · -- Case p % 24 = 11
      right
      use 11
      all_goals
        norm_num [h]
    · -- Case p % 24 = 13
      right
      use 13
      all_goals
        norm_num [h]
    · -- Case p % 24 = 17
      right
      use 17
      all_goals
        norm_num [h]
    · -- Case p % 24 = 19
      right
      use 19
      all_goals
        norm_num [h]
    · -- Case p % 24 = 23
      right
      use 23
      all_goals
        norm_num [h]