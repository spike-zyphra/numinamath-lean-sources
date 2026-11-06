import Mathlib

theorem number_theory_255597 (p : ℕ) (hp : Nat.Prime p) (h : 5 ≤ p) (h1 : Nat.Prime (2 * p + 1)) :
    ¬Nat.Prime (4 * p + 1) := by
  have h2 : p % 3 = 1 ∨ p % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h3 : p % 3 = 0 := by
      omega
    have h4 : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show (3 : ℕ) ∣ p by 
          omega
        )
      all_goals omega
    contradiction
  rcases h2 with (h2 | h2)
  · -- Assume p ≡ 1 (mod 3)
    have h3 : (2 * p + 1) % 3 = 0 := by
      omega
    have h4 : ¬Nat.Prime (2 * p + 1) := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (2 * p + 1) by 
        omega
      )
      all_goals omega
    contradiction 
  · -- Assume p ≡ 2 (mod 3)
    have h3 : (4 * p + 1) % 3 = 0 := by 
      omega
    have h4 : ¬Nat.Prime (4 * p + 1) := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (4 * p + 1) by 
        omega
      )
      all_goals omega
    exact h4