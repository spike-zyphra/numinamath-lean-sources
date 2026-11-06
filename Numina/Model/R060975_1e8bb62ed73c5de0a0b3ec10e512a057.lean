import Mathlib

theorem number_theory_123351 (p : ℕ) (hp : p.Prime) (h : 5 ≤ p) : 24 ∣ (p ^ 2 - 1) := by 
  have h1 : p % 2 ≠ 0 := by 
    by_contra h2
    have : ¬ p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
    contradiction
  
  have h2 : p % 3 ≠ 0 := by
    by_contra h3
    have h3' : 3 ∣ p := by
      omega
    have : ¬ p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt h3' (by omega) (by omega)
    contradiction
  
  have h3 : p % 3 = 1 ∨ p % 3 = 2 := by 
    omega
  
  have h4 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by 
    have h5 : p % 2 = 1 := by
      omega
    omega
  
  -- Now for any residue of p modulo 8. Let's show that p ^ 2 ≡ 1 (mod 8)
  have h8 : (p ^ 2) % 8 = 1 := by 
    rcases h4 with (h4 | h4 | h4 | h4)
    · simp [Nat.pow_mod, h4]
    · simp [Nat.pow_mod, h4]
    · simp [Nat.pow_mod, h4]
    · simp [Nat.pow_mod, h4]

  have h3' : (p ^ 2) % 3 = 1 := by
    rcases h3 with (h3 | h3)
    · simp [Nat.pow_mod, h3]
    · simp [Nat.pow_mod, h3]

  omega