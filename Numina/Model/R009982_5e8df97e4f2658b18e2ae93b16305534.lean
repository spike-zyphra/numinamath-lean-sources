import Mathlib

theorem number_theory_183991 (p : ℕ) (hp : Nat.Prime p) (h : 3 < p) :
    (p ^ 2) % 12 = 1 := by
  have h1 : p % 2 ≠ 0 := by
    by_contra h2
    have h4 : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals linarith
    contradiction

  have h2 : p % 3 ≠ 0 := by
    by_contra h3
    have h4 : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
      all_goals linarith
    contradiction
  
  have h5 : p % 2 = 1 := by omega
  have h7 : (p % 3) = 1 ∨ (p % 3) = 2 := by
    omega
  
  have h8 : (p ^ 2) % 3 = 1 := by 
    rcases h7 with (h7 | h7)
    · -- Case p ≡ 1 (mod 3)
      simp [Nat.pow_mod, h7]
    · -- Case p ≡ 2 (mod 3)
      simp [Nat.pow_mod, h7]

  have h6 : p % 4 = 1 ∨ p % 4 = 3 := by 
    have hp2 : p % 2 = 1 := by omega
    omega
  
  have h12 : (p ^ 2) % 4 = 1 := by 
    rcases h6 with (h6 | h6)
    · -- Case p ≡ 1 (mod 4)
      simp [Nat.pow_mod, h6]
    · -- Case p ≡ 3 (mod 4)
      simp [Nat.pow_mod, h6]

  omega