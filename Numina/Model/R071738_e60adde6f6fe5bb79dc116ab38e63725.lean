import Mathlib

theorem number_theory_194142 (p : ℕ) [hp : Fact (Nat.Prime p)] (hp1 : 5 ≤ p) : 24 ∣ (p ^ 2 - 1) := by
  have h1 : p ≥ 5 := hp1
  have h2 : Nat.Prime p := hp.1
  have h3 : p % 2 ≠ 0 := by
    by_contra h
    have h4 : ¬ Nat.Prime p := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
    have h5 : Nat.Prime p := h2
    contradiction
  have h5 : p % 3 ≠ 0 := by 
    by_contra h
    have h6 : 3 ∣ p := by omega
    have h7 : ¬ Nat.Prime p := by 
      apply Nat.not_prime_of_dvd_of_lt h6 (by omega) (by omega)
    have h8 : Nat.Prime p := h2
    contradiction 
  have h7 : (p ^ 2) % 8 = 1 := by 
    have h8 : p % 2 ≠ 0 := h3 
    have h9 : p % 2 = 1 := by omega 
    have h10 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by 
      omega 
    rcases h10 with (h | h | h | h) <;> simp [Nat.pow_mod, h] <;> omega 
  have h8 : (p ^ 2) % 3 = 1 := by 
    have h9 : p % 3 = 1 ∨ p % 3 = 2 := by 
      omega 
    rcases h9 with (h | h) 
    · -- Case p % 3 = 1 
      simp [Nat.pow_mod, h] 
    · -- Case p % 3 = 2 
      simp [Nat.pow_mod, h] 
  omega