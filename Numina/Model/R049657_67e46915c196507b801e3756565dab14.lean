import Mathlib

open Nat

theorem number_theory_2183
  (p : ℕ)
  (h₀ : Nat.Prime p)
  (h₁ : 5 < p) :
  10 ∣ (p ^ 4 - 1) := by
    have h2 : p % 10 = 1 ∨ p % 10 = 3 ∨ p % 10 = 7 ∨ p % 10 = 9 := by
      have h3 : p % 2 ≠ 0 := by
          by_contra h4
          have h5 : ¬ Nat.Prime p := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
            all_goals
              omega
          contradiction
      have h4 : p % 5 ≠ 0 := by
          by_contra h5
          have h6 : ¬ Nat.Prime p := by
            apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega)
            all_goals
              omega
          contradiction
      
      omega

    rcases h2 with (h2 | h2 | h2 | h2)
    · -- Case p % 10 = 1
      have h3 : (p ^ 4) % 10 = 1 := by
        have h4 : p % 10 = 1 := by
          exact h2
        norm_num [Nat.pow_mod, h4]
      omega
    · -- Case p % 10 = 3
      have h3 : (p ^ 4) % 10 = 1 := by
        have h4 : p % 10 = 3 := by
          exact h2
        norm_num [Nat.pow_mod, h4]
      omega
    · -- Case p % 10 = 7
      have h3 : (p ^ 4) % 10 = 1 := by
        have h4 : p % 10 = 7 := by
          exact h2
        norm_num [Nat.pow_mod, h4]
      omega
    · -- Case p % 10 = 9
      have h3 : (p ^ 4) % 10 = 1 := by
        have h4 : p % 10 = 9 := by
          exact h2
        norm_num [Nat.pow_mod, h4]
      omega