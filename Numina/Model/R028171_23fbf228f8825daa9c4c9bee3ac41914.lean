import Mathlib

theorem number_theory_254853 {p : ℕ} (hp : Nat.Prime p) :
    Nat.Prime (p^2 + 2007 * p - 1) ↔ p = 3 := by
  constructor
  · -- Assume Nat.Prime (p^2 + 2007 * p - 1), prove p = 3
    intro h
    by_cases h2 : p > 3
    · -- Assume p > 3
      have h3 : p % 3 = 1 ∨ p % 3 = 2 := by 
        by_contra h
        push_neg at h
        have h4 : p % 3 = 0 := by 
          omega
        have h5 : p ≠ 3 := by
          omega
        have h6 : p > 3 := by 
          omega
        have h7 : ¬Nat.Prime p := by 
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
        contradiction 
      rcases h3 with (h3 | h3)
      · -- p % 3 = 1
        have h4 : (p ^ 2 + 2007 * p - 1) % 3 = 0 := by 
          have h3p : p % 3 = 1 := h3 
          have h5 : p ^ 2 % 3 = 1 := by 
            have h1 : p % 3 = 1 := h3p 
            simp [Nat.pow_mod, h1] 
          have h6 : (2007 * p) % 3 = 0 := by 
            have h1 : p % 3 = 1 := h3p 
            simp [Nat.mul_mod, h1] 
          omega 
        have h8 : ¬Nat.Prime (p ^ 2 + 2007 * p - 1) := by 
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p ^ 2 + 2007 * p - 1) by omega)
          all_goals
            have h1 : p ^ 2 + 2007 * p - 1 > 3 := by
              have hp3 : p > 3 := h2
              have hp3 : p ≥ 4 := by omega
              have : p^2 + 2007 * p - 1 ≥ 4^2 + 2007 * 4 - 1 := by 
                have hp3 : p ≥ 4 := by omega 
                have h1 : p ^ 2 ≥ 4 ^ 2 := by nlinarith 
                have h2 : 2007 * p ≥ 2007 * 4 := by 
                  nlinarith 
                omega 
              omega 
            all_goals 
              omega 
        contradiction
      · -- p % 3 = 2
        have h4 : (p ^ 2 + 2007 * p - 1) % 3 = 0 := by 
          have h3p : p % 3 = 2 := h3 
          have h5 : p ^ 2 % 3 = 1 := by 
            have h1 : p % 3 = 2 := h3p 
            simp [Nat.pow_mod, h1] 
          have h6 : (2007 * p) % 3 = 0 := by 
            have h1 : p % 3 = 2 := h3p 
            simp [Nat.mul_mod, h1] 
          omega 
        have h8 : ¬Nat.Prime (p ^ 2 + 2007 * p - 1) := by 
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p ^ 2 + 2007 * p - 1) by omega)
          all_goals
            have h1 : p ^ 2 + 2007 * p - 1 > 3 := by
              have hp3 : p > 3 := h2
              have hp3 : p ≥ 4 := by omega
              have : p^2 + 2007 * p - 1 ≥ 4^2 + 2007 * 4 - 1 := by 
                have hp3 : p ≥ 4 := by omega 
                have h1 : p ^ 2 ≥ 4 ^ 2 := by nlinarith 
                have h2 : 2007 * p ≥ 2007 * 4 := by 
                  nlinarith 
                omega 
              omega 
            all_goals 
              omega 
        contradiction
    · -- Assume p ≤ 3
      have h4 : p ≤ 3 := by 
        omega 
      interval_cases p <;> norm_num at hp h ⊢ 
      <;> tauto 
  · -- Assume p = 3 
    intro hp3 
    rw [hp3] 
    all_goals norm_num