import Mathlib

theorem number_theory_261215 (p : ℕ) (hp : p.Prime) (hp1 : (p + 10).Prime) (hp2 : (p + 14).Prime) :
    p = 3 := by
  by_cases h : p ≤ 3
  · -- Case where p ≤ 3
    interval_cases p <;> norm_num at hp hp1 hp2 ⊢ <;> try { tauto }
  
  · -- Case where p > 3
    push_neg at h
    have h1 : p % 3 = 1 ∨ p % 3 = 2 := by 
      have h3 : p % 3 = 0 → ¬ p.Prime := by
        intro h4
        apply Nat.not_prime_of_dvd_of_lt (show (3 : ℕ) ∣ p by omega)
        all_goals omega
      have : p % 3 = 1 ∨ p % 3 = 2 := by 
        have h6 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by 
          omega
          all_goals omega
        rcases h6 with (h6 | h6 | h6)
        · -- Contradiction if p ≡ 0 (mod 3)
          have h7 : ¬ p.Prime := h3 h6
          contradiction
        · -- Case p ≡ 1 (mod 3)
          omega
        · -- Case p ≡ 2 (mod 3)
          omega
      assumption

    rcases h1 with (h1 | h1)
    
    · -- Case p ≡ 1 (mod 3)
      have h2 : (p + 14) % 3 = 0 := by 
        omega
      have h3 : ¬ (p + 14).Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show (3 : ℕ) ∣ (p + 14) by omega)
        all_goals omega
      contradiction
  
    · -- Case p ≡ 2 (mod 3)
      have h2 : (p + 10) % 3 = 0 := by 
        omega
      have h3 : ¬ (p + 10).Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show (3 : ℕ) ∣ (p + 10) by omega)
        all_goals omega
      contradiction