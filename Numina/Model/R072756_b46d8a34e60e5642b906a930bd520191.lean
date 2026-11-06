import Mathlib

theorem number_theory_112111 (p : ℕ) (hp : Nat.Prime p) (h : Nat.Prime (p + 10)) (h' : Nat.Prime (p + 14)) :
    p = 3 := by 
  by_cases h1 : p ≤ 3 
  · interval_cases p <;> 
     norm_num at hp h h' 
    <;> try tauto
  · -- Case p > 3
    have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
      by_contra h3 
      push_neg at h3 
      have h4 : (p : ℕ) % 3 = 0 := by omega 
      have h5 : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals linarith
      contradiction 
    rcases h2 with (h2 | h2)
    · -- Case p ≡ 1 (mod 3)
      have h4 : (p + 14) % 3 = 0 := by 
        omega 
      have h5 : ¬ Nat.Prime (p + 14) := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 14) by omega)
        all_goals linarith
      contradiction 
      all_goals linarith
    · -- Case p ≡ 2 (mod 3)
      have h4 : (p + 10) % 3 = 0 := by 
        omega 
      have h5 : ¬ Nat.Prime (p + 10) := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 10) by omega)
        all_goals linarith
      contradiction 
      all_goals linarith