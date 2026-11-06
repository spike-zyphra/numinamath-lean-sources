import Mathlib

theorem number_theory_151030 (p : ℕ) (hp : Nat.Prime p) (h : p > 3) :
    12 ∣ (p ^ 2 - 1) := by
  have h1 : p % 2 ≠ 0 := by
    by_contra h2
    have h4 : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals linarith
    contradiction

  have h2 : p % 3 ≠ 0 := by
    by_contra h3
    have h4 : 3 ∣ p := by
      omega
    have h5 : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt h4
      all_goals linarith
    contradiction
  
  have h3 : p % 4 = 1 ∨ p % 4 = 3 := by
    omega
  
  have h4 : p % 3 = 1 ∨ p % 3 = 2 := by
    omega

  have h5 : (p : ℕ) ^ 2 % 4 = 1 := by
    have h6 : p % 4 = 1 ∨ p % 4 = 3 := h3
    rcases h6 with (h6 | h6)
    · 
      simp [Nat.pow_mod, h6]
    · 
      simp [Nat.pow_mod, h6]

  have h5' : (p : ℕ) ^ 2 % 3 = 1 := by
    have h6 : p % 3 = 1 ∨ p % 3 = 2 := h4
    rcases h6 with (h6 | h6)
    · 
      simp [Nat.pow_mod, h6]
    · 
      simp [Nat.pow_mod, h6]

  have h6 : (p ^ 2) % 12 = 1 := by
    omega
  
  have h7 : (p ^ 2 - 1) % 12 = 0 := by
    omega
  
  exact Nat.dvd_of_mod_eq_zero h7