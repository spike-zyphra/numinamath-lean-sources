import Mathlib

theorem number_theory_293600 (p : ℕ) (hp : p.Prime ∧ (p + 2).Prime ∧ (p + 4).Prime) :
    p = 3 := by 
  rcases hp with ⟨h1, h2, h3⟩
  by_cases h4 : p ≤ 3
  · interval_cases p <;> trivial
  · -- Case where p > 3

    have h5 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by 
      omega

    rcases h5 with (h5 | h5 | h5)
    
    · -- Case where p % 3 = 0

      have h6 : ¬ p.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega

      contradiction

    · -- Case where p % 3 = 1

      have h7 : (p + 2) % 3 = 0 := by 
        omega

      have h8 : ¬ (p + 2).Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 2) by omega)
        all_goals omega

      contradiction

    · -- Case where p % 3 = 2

      have h9 : (p + 4) % 3 = 0 := by 
        omega

      have h10 : ¬ (p + 4).Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 4) by omega)
        all_goals omega

      contradiction