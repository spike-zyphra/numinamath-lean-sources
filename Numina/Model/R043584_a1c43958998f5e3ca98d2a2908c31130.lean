import Mathlib

theorem number_theory_213541 (A : ℕ) (hA : A.Prime) (hA1 : (A + 14).Prime)
    (hA2 : (A + 18).Prime) (hA3 : (A + 32).Prime) (hA4 : (A + 36).Prime) :
    A = 5 := by
  by_cases h : A ≤ 5
  · interval_cases A <;> norm_num at hA hA1 hA2 hA3 hA4 ⊢ <;> try { trivial }
  · -- A > 5
    have h1 : A % 5 = 0 ∨ A % 5 = 1 ∨ A % 5 = 2 ∨ A % 5 = 3 ∨ A % 5 = 4 := by omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1)
    · -- A % 5 = 0
      have h2 : ¬ A.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ A by omega)
        all_goals linarith
      contradiction
    · -- A % 5 = 1
      have h2 : (A + 14) % 5 = 0 := by
        omega
      have h3 : ¬ (A + 14).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (A + 14) by omega)
        all_goals linarith
      contradiction
    · -- A % 5 = 2
      have h2 : (A + 18) % 5 = 0 := by
        omega
      have h3 : ¬ (A + 18).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (A + 18) by omega)
        all_goals linarith
      contradiction
    · -- A % 5 = 3
      have h2 : (A + 32) % 5 = 0 := by
        omega
      have h3 : ¬ (A + 32).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (A + 32) by omega)
        all_goals linarith
      contradiction
    · -- A % 5 = 4
      have h2 : (A + 36) % 5 = 0 := by
        omega
      have h3 : ¬ (A + 36).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (A + 36) by omega)
        all_goals linarith
      contradiction