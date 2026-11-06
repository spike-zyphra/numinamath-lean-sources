import Mathlib

theorem number_theory_174705 (p : ℕ) (hp : p.Prime) :
    (4 * p^2 + 1).Prime ∧ (6 * p^2 + 1).Prime ↔ p = 5 := by
  constructor
  · -- Assume that both $4p^2+1$ and $6p^2+1$ are prime, show $p = 5$.
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h3 : p > 5
    · -- p > 5 
      have h4 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
        have h5 : p % 5 ≠ 0 := by 
          by_contra h
          have h6 : p % 5 = 0 := by omega 
          have h7 : ¬p.Prime := by 
            apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega)
            all_goals omega 
          tauto 
        omega 
      rcases h4 with (h4 | h4 | h4 | h4)
      · -- p ≡ 1 (mod 5)
        have h8 : (4 * p ^ 2 + 1) % 5 = 0 := by 
          have h9 : p % 5 = 1 := h4 
          have h10 : p ^ 2 % 5 = 1 := by 
            simp [Nat.pow_mod, h9]
          omega 
        -- Show that (4p^2+1) is not prime, contradiction
        have h10 : ¬(4 * p ^ 2 + 1).Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ 4 * p ^ 2 + 1 by omega)
          all_goals nlinarith [show 4 * p ^ 2 + 1 > 1 by nlinarith [h3]]
        contradiction 
      · -- p ≡ 2 (mod 5)
        have h8 : (6 * p ^ 2 + 1) % 5 = 0 := by 
          have h9 : p % 5 = 2 := h4 
          have h10 : p ^ 2 % 5 = 4 := by 
            simp [Nat.pow_mod, h9]
          omega 
        -- Show that (6p^2+1) is not prime, contradiction 
        have h11 : ¬(6 * p ^ 2 + 1).Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ 6 * p ^ 2 + 1 by omega)
          all_goals nlinarith [show 6 * p ^ 2 + 1 > 1 by nlinarith [h3]]
        contradiction 
      · -- p ≡ 3 (mod 5)
        have h8 : (6 * p ^ 2 + 1) % 5 = 0 := by 
          have h9 : p % 5 = 3 := h4 
          have h10 : p ^ 2 % 5 = 4 := by 
            simp [Nat.pow_mod, h9]
          omega 
        -- Show that (6p^2+1) is not prime, contradiction 
        have h11 : ¬(6 * p ^ 2 + 1).Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ 6 * p ^ 2 + 1 by omega)
          all_goals nlinarith [show 6 * p ^ 2 + 1 > 1 by nlinarith [h3]]
        contradiction
      · -- p ≡ 4 (mod 5)
        have h8 : (4 * p ^ 2 + 1) % 5 = 0 := by 
          have h9 : p % 5 = 4 := h4 
          have h10 : p ^ 2 % 5 = 1 := by
            simp [Nat.pow_mod, h9]
          omega 
        -- Show that (4p^2+1) is not prime, contradiction 
        have h10 : ¬(4 * p ^ 2 + 1).Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ 4 * p ^ 2 + 1 by omega)
          all_goals nlinarith [show 4 * p ^ 2 + 1 > 1 by nlinarith [h3]]
        contradiction
    · -- p ≤ 5 
      interval_cases p <;> norm_num at hp h1 h2 ⊢ <;> tauto 
  · -- Assume p = 5, show both $4p^2+1$ and $6p^2+1$ are prime.
    intro hp 
    rw [hp] 
    constructor <;> norm_num