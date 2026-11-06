import Mathlib

theorem number_theory_197105 (p : ℕ) (hp : p.Prime) (h : 3 < p) :
    24 ∣ p^2 - 1 := by

  have h1 : p % 2 = 1 := by
    have h2 : p % 2 = 1 ∨ p % 2 = 0 := by omega
    rcases h2 with (h2 | h2)
    · exact h2
    · -- if p % 2 = 0 then p is not prime
      have h3 : p ≥ 4 := by linarith
      have h4 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
        all_goals omega
      contradiction
  
  have h8 : (p ^ 2) % 8 = 1 := by
    have h5 : p % 2 = 1 := h1
    have h6 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
      omega
    rcases h6 with (h6 | h6 | h6 | h6)
    · -- p ≡ 1 [MOD 8]
      simp [Nat.pow_mod, h6]
    · -- p ≡ 3 [MOD 8]
      simp [Nat.pow_mod, h6]
    · -- p ≡ 5 [MOD 8]
      simp [Nat.pow_mod, h6]
    · -- p ≡ 7 [MOD 8]
      simp [Nat.pow_mod, h6]

  have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
    have h3 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases h3 with (h3 | h3 | h3)
    · -- if p % 3 = 0 then p is not prime
      have h4 : p ≥ 4 := by linarith
      have h5 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega
      contradiction
    · exact Or.inl h3
    · exact Or.inr h3

  have h3 : (p ^ 2) % 3 = 1 := by
    have h4 : p % 3 = 1 ∨ p % 3 = 2 := h2
    rcases h4 with (h4 | h4)
    · -- p ≡ 1 [MOD 3]
      simp [Nat.pow_mod, h4]
    · -- p ≡ 2 [MOD 3]
      simp [Nat.pow_mod, h4]

  have h4 : (p ^ 2) % 8 = 1 := h8
  have h5 : (p ^ 2) % 3 = 1 := h3
  
  omega