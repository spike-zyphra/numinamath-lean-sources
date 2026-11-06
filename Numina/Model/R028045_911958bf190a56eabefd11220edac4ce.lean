import Mathlib

theorem number_theory_101737 :
    IsGreatest {n : ℕ | Even n ∧ ¬∃ a b, Odd a ∧ Odd b ∧ a + b = n ∧ ¬Nat.Prime a ∧ ¬Nat.Prime b} 38 := by
  constructor
  · -- Show 38 is in the set.
    constructor
    · -- Show 38 is even.
      exact Nat.even_iff.mpr (by norm_num)
    · -- Show 38 cannot be expressed as the sum of two composite odd positive integers.
      intro h
      rcases h with ⟨a, b, h1, h2, h3, h4, h5⟩
      have h6 : a ≤ 38 := by
        omega
      have h7 : b ≤ 38 := by
        omega
      have h8 : a % 2 = 1 := by
        rcases h1 with ⟨k, hk⟩
        omega
      have h9 : b % 2 = 1 := by
        rcases h2 with ⟨k, hk⟩
        omega
      interval_cases a <;> try { 
        omega 
      } <;> try { 
        interval_cases b <;> norm_num at h4 h5 h1 h2 h3 
      }
  · -- Show 38 is the greatest such integer.
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    by_contra h
    push_neg at h
    have h4 : n > 38 := by linarith
    have h3 : ∃ a b, Odd a ∧ Odd b ∧ a + b = n ∧ ¬Nat.Prime a ∧ ¬Nat.Prime b := by
      have h9 : n % 2 = 0 := by
        obtain ⟨k, hk⟩ := hn1
        omega
      have h11 : n > 38 := h4
      have h10 : n % 6 = 0 ∨ n % 6 = 2 ∨ n % 6 = 4 := by 
        omega
      rcases h10 with (h10 | h10 | h10)
      · -- If n ≡ 0 [6]
        use 9, n - 9
        constructor
        · -- Show 9 is odd.
          exact Nat.odd_iff.mpr (by norm_num)
        constructor
        · -- Show n - 9 is odd
          have : (n - 9) % 2 = 1 := by
            omega
          exact Nat.odd_iff.mpr this
        constructor
        · -- Show 9 + (n - 9) = n
          omega
        constructor
        · -- Show 9 is not prime
          norm_num
        · -- Show n - 9 is not prime
          have h33 : n - 9 ≥ 33 := by
            omega
          have h111 : (n - 9) % 3 = 0 := by
            omega
          have h333 : ¬Nat.Prime (n - 9) := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (n - 9) by omega)
            all_goals
              omega
          exact h333
      · -- If n ≡ 2 [6]
        use 35, n - 35
        constructor
        · -- Show 35 is odd.
          exact Nat.odd_iff.mpr (by norm_num)
        constructor
        · -- Show n - 35 is odd
          have : (n - 35) % 2 = 1 := by
            omega
          exact Nat.odd_iff.mpr this
        constructor
        · -- Show 35 + (n - 35) = n
          omega
        constructor
        · -- Show 35 is not prime
          norm_num
        · -- Show n - 35 is not prime
          have h33 : n - 35 ≥ 9 := by
            omega
          have h111 : (n - 35) % 3 = 0 := by
            omega
          have h333 : ¬Nat.Prime (n - 35) := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (n - 35) by omega)
            all_goals
              omega
          exact h333
      · -- If n ≡ 4 [6]
        use 25, n - 25
        constructor
        · -- Show 25 is odd.
          exact Nat.odd_iff.mpr (by norm_num)
        constructor
        · -- Show n - 25 is odd
          have : (n - 25) % 2 = 1 := by
            omega
          exact Nat.odd_iff.mpr this
        constructor
        · -- Show 25 + (n - 25) = n
          omega
        constructor
        · -- Show 25 is not prime
          norm_num
        · -- Show n - 25 is not prime
          have h33 : n - 25 ≥ 9 := by
            omega
          have h111 : (n - 25) % 3 = 0 := by
            omega
          have h333 : ¬Nat.Prime (n - 25) := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (n - 25) by omega)
            all_goals
              omega
          exact h333
    contradiction