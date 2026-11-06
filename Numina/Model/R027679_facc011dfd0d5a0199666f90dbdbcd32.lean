import Mathlib

theorem number_theory_213189 (p : ℕ) (hp : p.Prime) :
    (p^2 - 6).Prime ∧ (p^2 + 6).Prime ↔ p = 5 := by
  constructor
  · -- Assume h : (p^2 - 6).Prime ∧ (p^2 + 6).Prime, prove p = 5
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h3 : p > 5
    · -- p > 5
      have h4 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
        by_contra h
        push_neg at h
        have h6 : p % 5 = 0 := by
          omega
        have h5 : p > 1 := by 
          omega 
        have h8 : ¬p.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega)
          all_goals omega 
        contradiction
      rcases h4 with (h4 | h4 | h4 | h4)
      · -- p ≡ 1 (mod 5)
        have h5 : (p ^ 2 - 6) % 5 = 0 := by 
          have h6 : p % 5 = 1 := h4 
          have h7 : p ^ 2 % 5 = 1 := by
            simp [Nat.pow_mod, h6]
          omega
        have h8 : p ^ 2 ≥ 36 := by
          have h9 : p ≥ 6 := by 
            omega 
          have h10 : p ^ 2 ≥ 36 := by 
            nlinarith 
          linarith
        have h9 : ¬(p ^ 2 - 6).Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p ^ 2 - 6 by omega)
          all_goals 
            omega 
        contradiction
      · -- p ≡ 2 (mod 5)
        have h5 : (p ^ 2 + 6) % 5 = 0 := by 
          have h6 : p % 5 = 2 := h4 
          have h7 : p ^ 2 % 5 = 4 := by
            simp [Nat.pow_mod, h6]
          omega
        have h8 : p ^ 2 ≥ 36 := by
          have h9 : p ≥ 6 := by 
            omega 
          have h10 : p ^ 2 ≥ 36 := by 
            nlinarith 
          linarith 
        have h9 : ¬(p ^ 2 + 6).Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p ^ 2 + 6 by omega)
          all_goals 
            omega 
        contradiction
      · -- p ≡ 3 (mod 5)
        have h5 : (p ^ 2 + 6) % 5 = 0 := by 
          have h6 : p % 5 = 3 := h4 
          have h7 : p ^ 2 % 5 = 4 := by 
            simp [Nat.pow_mod, h6]
          omega
        have h8 : p ^ 2 ≥ 36 := by
          have h9 : p ≥ 6 := by 
            omega 
          have h10 : p ^ 2 ≥ 36 := by 
            nlinarith 
          linarith 
        have h9 : ¬(p ^ 2 + 6).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p ^ 2 + 6 by omega)
          all_goals 
            omega 
        contradiction 
      · -- p ≡ 4 (mod 5)
        have h5 : (p ^ 2 - 6) % 5 = 0 := by 
          have h6 : p % 5 = 4 := h4 
          have h7 : p ^ 2 % 5 = 1 := by
            simp [Nat.pow_mod, h6]
          omega 
        have h8 : p ^ 2 ≥ 36 := by
          have h9 : p ≥ 6 := by 
            omega 
          have h10 : p ^ 2 ≥ 36 := by 
            nlinarith 
          linarith 
        have h9 : ¬(p ^ 2 - 6).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p ^ 2 - 6 by omega)
          all_goals 
            omega 
        contradiction 
    · -- p ≤ 5
      have h4 : p ≤ 5 := by 
        omega 
      interval_cases p <;> norm_num at hp h1 h2 ⊢ <;> tauto 
  · -- Assume p = 5, prove both are primes
    intro hp 
    rw [hp] 
    constructor <;> norm_num