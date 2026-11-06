import Mathlib

theorem number_theory_233564 (p : ℕ) (hp : p.Prime) (hp1 : (p + 10).Prime) (hp2 : (p + 14).Prime) :
    p = 3 := by
  by_cases h : p ≤ 23
  · interval_cases p <;> norm_num at hp hp1 hp2 ⊢ <;> all_goals tauto
  · -- Now, let's consider the case where p > 23.
    have h1 : p > 23 := by linarith
    have h2 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
      omega
    rcases h2 with (h2 | h2 | h2)
    · -- Case where p % 3 = 0
      have h3 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals linarith
      contradiction
    · -- Case where p % 3 = 1
      have h4 : (p + 14) % 3 = 0 := by
        omega
      have h5 : ¬(p + 14).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 14) by omega)
        all_goals
          omega
      contradiction
    · -- Case where p % 3 = 2
      have h6 : (p + 10) % 3 = 0 := by
        omega
      have h7 : ¬(p + 10).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 10) by omega)
        all_goals
          omega
      contradiction