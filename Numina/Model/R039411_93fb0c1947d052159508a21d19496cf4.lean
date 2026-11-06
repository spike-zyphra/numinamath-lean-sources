import Mathlib

theorem number_theory_104601 (p : ℕ) (hp : Nat.Prime p) :
    Nat.Prime (4 * p ^ 2 + 1) ∧ Nat.Prime (6 * p ^ 2 + 1) ↔ p = 5 := by
  constructor
  · -- Assume Nat.Prime (4 * p ^ 2 + 1) ∧ Nat.Prime (6 * p ^ 2 + 1) holds, prove p = 5
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h3 : p ≤ 5
    · -- p is less than or equal to 5
      interval_cases p <;> norm_num at hp h1 h2 ⊢
      <;> tauto
    · -- p > 5
      have h4 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 ∨ p % 5 = 0 := by
        omega
      have h5 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by 
        by_contra h
        push_neg at h
        have h6 : p % 5 = 0 := by 
          omega
        have h7 : p > 1 := by
          nlinarith
        have h8 : ¬Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega)
          all_goals
            omega
        contradiction
      rcases h5 with (h | h | h | h)
      · -- Assume p % 5 = 1
        have h8 : (4 * p ^ 2 + 1) % 5 = 0 := by
          have h10 : p % 5 = 1 := h
          have h11 : p ^ 2 % 5 = 1 := by
            simp [Nat.pow_mod, h10]
          omega
        have h9 : ¬Nat.Prime (4 * p ^ 2 + 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (4 * p ^ 2 + 1) by omega)
          all_goals 
            nlinarith [h8, show (4 * p ^ 2 + 1) > 1 by nlinarith, show 5 > 1 by norm_num]
        contradiction
      · -- Assume p % 5 = 2
        have h8 : (6 * p ^ 2 + 1) % 5 = 0 := by
          have h10 : p % 5 = 2 := h
          have h11 : p ^ 2 % 5 = 4 := by
            simp [Nat.pow_mod, h10]
          omega
        have h9 : ¬Nat.Prime (6 * p ^ 2 + 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (6 * p ^ 2 + 1) by omega)
          all_goals 
            nlinarith [h8, show (6 * p ^ 2 + 1) > 1 by nlinarith, show 5 > 1 by norm_num]
        contradiction
      · -- Assume p % 5 = 3
        have h8 : (6 * p ^ 2 + 1) % 5 = 0 := by
          have h10 : p % 5 = 3 := h
          have h11 : p ^ 2 % 5 = 4 := by
            simp [Nat.pow_mod, h10]
          omega
        have h9 : ¬Nat.Prime (6 * p ^ 2 + 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (6 * p ^ 2 + 1) by omega)
          all_goals 
            nlinarith [h8, show (6 * p ^ 2 + 1) > 1 by nlinarith, show 5 > 1 by norm_num]
        contradiction
      · -- Assume p % 5 = 4
        have h8 : (4 * p ^ 2 + 1) % 5 = 0 := by
          have h10 : p % 5 = 4 := h
          have h11 : p ^ 2 % 5 = 1 := by
            simp [Nat.pow_mod, h10]
          omega
        have h9 : ¬Nat.Prime (4 * p ^ 2 + 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (4 * p ^ 2 + 1) by omega)
          all_goals 
            nlinarith [h8, show (4 * p ^ 2 + 1) > 1 by nlinarith, show 5 > 1 by norm_num]
        contradiction
  · -- Assume p = 5, prove Nat.Prime (4 * p ^ 2 + 1) ∧ Nat.Prime (6 * p ^ 2 + 1)
    intro hp_eq
    rw [hp_eq]
    constructor
    · norm_num
    · norm_num