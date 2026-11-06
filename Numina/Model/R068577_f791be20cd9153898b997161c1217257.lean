import Mathlib

theorem number_theory_255604 :
    ∀ p : ℕ, p.Prime ∧ p > 3 → p % 6 = 1 ∨ p % 6 = 5 := by
  intro p hp
  have h1 : p.Prime := hp.1
  have h2 : p > 3 := hp.2

  have h3 : p % 2 ≠ 0 := by
    by_contra h
    have : ¬p.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) 
      all_goals linarith
    contradiction

  have h4 : p % 3 ≠ 0 := by
    by_contra h
    have : ¬p.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) 
      all_goals linarith
    contradiction
  
  have : p % 6 = 1 ∨ p % 6 = 5 := by
    omega

  exact this