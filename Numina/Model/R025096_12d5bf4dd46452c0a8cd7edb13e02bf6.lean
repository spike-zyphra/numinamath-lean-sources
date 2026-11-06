import Mathlib

theorem number_theory_236150 :
    ∃ n : ℕ, Nat.Prime (n - 96) ∧ Nat.Prime n ∧ Nat.Prime (n + 96) ∧
    ¬∃ n : ℕ, Nat.Prime (n - 1996) ∧ Nat.Prime n ∧ Nat.Prime (n + 1996) := by
  use 101
  constructor
  · -- Show 101 - 96 = 5 is prime
    norm_num
  constructor
  · -- Show 101 is prime
    norm_num
  constructor
  · -- Show 101 + 96 = 197 is prime
    norm_num
  · -- Show that there's no n such that n-1996, n, n+1996 are all primes
    intro h
    rcases h with ⟨n, hn1, hn2, hn3⟩
    by_cases h1 : n > 1996
    · -- Assume n > 1996
      have h1' : n - 1996 + 1996 = n := by
        omega
      have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
        omega
      rcases h2 with (h2 | h2 | h2)
      · -- Case n ≡ 0 (mod 3)
        have h3 : ¬Nat.Prime n := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ n by omega)
          all_goals omega
        contradiction
      · -- Case n ≡ 1 (mod 3)
        have h1' : n ≥ 1997 := by omega
        have h3 : (n - 1996) % 3 = 0 := by 
          omega
        have h4 : n - 1996 ≥ 1 := by 
          omega
        by_cases h5 : n - 1996 > 3
        · -- Case n - 1996 > 3
          have h6 : ¬Nat.Prime (n - 1996) := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (n - 1996) by omega)
            all_goals omega
          have h7 : Nat.Prime (n - 1996) := hn1
          exact h6 h7
        · -- Case n - 1996 ≤ 3
          have h6 : n - 1996 ≤ 3 := by
            omega
          have h9 : n - 1996 = 0 ∨ n - 1996 = 1 ∨ n - 1996 = 2 ∨ n - 1996 = 3 := by 
            interval_cases h : n - 1996 <;> omega
          rcases h9 with (h9 | h9 | h9 | h9)
          · -- Case n - 1996 = 0
            have h10 : n - 1996 = 0 := by
              omega
            rw [h10] at hn1
            norm_num at hn1
          · -- Case n - 1996 = 1
            have h10 : n - 1996 = 1 := by
              omega
            rw [h10] at hn1
            norm_num at hn1
          · -- Case n - 1996 = 2
            have h10 : n - 1996 = 2 := by
              omega
            have h11 : n = 1998 := by
              omega
            rw [h11] at hn2
            norm_num at hn2
          · -- Case n - 1996 = 3
            have h10 : n - 1996 = 3 := by
              omega
            have h11 : n = 1999 := by
              omega
            rw [h11] at hn3
            norm_num at hn3
      · -- Case n ≡ 2 (mod 3)
        have h3 : (n + 1996) % 3 = 0 := by
          omega
        have h5 : n + 1996 > 3 := by
          omega
        have h6 : ¬Nat.Prime (n + 1996) := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (n + 1996) by omega)
          all_goals omega
        contradiction
    · -- Assume n ≤ 1996
      have h4 : n ≤ 1996 := by
        omega
      have h5 : n - 1996 = 0 := by
        omega
      rw [h5] at hn1
      norm_num at hn1