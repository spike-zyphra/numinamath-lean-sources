import Mathlib
/-In a certain month, the dates of three of the Sundays are prime. On what day does the 7th of the month fall? A Thursday B Friday C Saturday D Monday E Tuesday-/
theorem number_theory_234617 (n : ℕ) (h₀ : n > 0) (h₁ : Nat.Prime n) (h₂ : Nat.Prime (n + 7)) (h₃ : Nat.Prime (n + 14)) :
    (n + 6) % 7 = 4 := by 
  -- note that we can classify by n % 3 --
  have h4 : n ≤ 3 := by
      by_contra! h
      have h5 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h5 with (h5 | h5 | h5)
      · -- n % 3 = 0
        have h6 : n ≠ 3 := by omega
        have h7 : ¬Nat.Prime n := by
          apply Nat.not_prime_of_dvd_of_lt (m := 3)
          · omega
          · omega
          · omega
        contradiction
      · -- n % 3 = 1
        have h7 : (n + 14) % 3 = 0 := by
          omega
        have h8 : n + 14 ≠ 3 := by omega
        have h9 : ¬Nat.Prime (n + 14) := by
          apply Nat.not_prime_of_dvd_of_lt (m := 3)
          · omega
          · omega
          · omega
        contradiction
      · -- n % 3 = 2
        have h7 : (n + 7) % 3 = 0 := by
          omega
        have h8 : n + 7 ≠ 3 := by omega
        have h9 : ¬Nat.Prime (n + 7) := by
          apply Nat.not_prime_of_dvd_of_lt (m := 3)
          · omega
          · omega
          · omega
        contradiction
  interval_cases n <;> norm_num at *