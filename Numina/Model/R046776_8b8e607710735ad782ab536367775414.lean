import Mathlib

theorem number_theory_290098 (p : ℕ) (hp : Nat.Prime p)
    (h3 : Nat.Prime (3 * p + 2)) (h5 : Nat.Prime (5 * p + 4)) (h7 : Nat.Prime (7 * p + 6))
    (h9 : Nat.Prime (9 * p + 8)) (h11 : Nat.Prime (11 * p + 10)) :
    ¬Nat.Prime (6 * p + 11) := by

  by_contra h
  have h_comm : Nat.Prime (6 * p + 11) := h

  by_cases h2 : p ≤ 11
  · -- Case p ≤ 11
    interval_cases p <;> norm_num at hp h3 h5 h7 h9 h11 h_comm <;> try { contradiction }
  
  · -- Case p > 11
    have h1 : p > 11 := by linarith

    have h2 : p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by 
      omega

    rcases h2 with (h2 | h2 | h2 | h2 | h2)
    · -- Case p % 5 = 0
      have h3a : ¬Nat.Prime p := by 
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega)
        all_goals
        omega
      contradiction

    · -- Case p % 5 = 1
      have h3b : (3 * p + 2) % 5 = 0 := by 
        omega
      have h4 : ¬Nat.Prime (3 * p + 2) := by 
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (3 * p + 2) by omega)
        all_goals 
        omega
      contradiction

    · -- Case p % 5 = 2
      have h3c : (7 * p + 6) % 5 = 0 := by 
        omega
      have h5 : ¬Nat.Prime (7 * p + 6) := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (7 * p + 6) by omega)
        all_goals
        omega
      contradiction

    · -- Case p % 5 = 3
      have h3d : (9 * p + 8) % 5 = 0 := by 
        omega
      have h6 : ¬Nat.Prime (9 * p + 8) := by 
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (9 * p + 8) by omega)
        all_goals
        omega
      contradiction

    · -- Case p % 5 = 4
      have h3e : (6 * p + 11) % 5 = 0 := by
        omega
      have h7 : ¬Nat.Prime (6 * p + 11) := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (6 * p + 11) by omega)
        all_goals
        omega
      contradiction