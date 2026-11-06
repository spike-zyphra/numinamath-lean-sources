import Mathlib

theorem number_theory_128181 (p : ℕ) (hp : p.Prime) (h : 5 ≤ p) : 12 ∣ (p^2 - 1) := by 
  have h1 : p % 2 ≠ 0 := by
    by_contra h2
    have h3 : ¬ p.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) 
        (by omega) (by omega)
    contradiction

  have h2 : p % 3 ≠ 0 := by 
    by_contra h3
    have h4 : 3 ∣ p := by 
      omega
    have h5 : ¬ p.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt h4 (by omega) (by omega)
    contradiction
  
  have h3 : p % 2 = 1 := by 
    omega

  have h4 : (p ^ 2) % 4 = 1 := by 
    have h1 : p % 4 = 1 ∨ p % 4 = 3 := by 
      omega
    rcases h1 with (h1 | h1)
    · 
      norm_num [Nat.pow_mod, h1] 
    · 
      norm_num [Nat.pow_mod, h1]

  have h5 : (p ^ 2) % 3 = 1 := by
    have h1 : p % 3 = 1 ∨ p % 3 = 2 := by 
      omega
    rcases h1 with (h1 | h1)
    · 
      norm_num [Nat.pow_mod, h1]
    · 
      norm_num [Nat.pow_mod, h1]

  have h6 : (p ^ 2) % 12 = 1 := by 
    omega
  omega