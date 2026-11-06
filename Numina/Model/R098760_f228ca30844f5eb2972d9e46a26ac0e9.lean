import Mathlib

theorem number_theory_128432 (p : ℕ) (hp : Nat.Prime p) :
    Nat.Prime (4 * p ^ 2 + 1) ∧ Nat.Prime (6 * p ^ 2 + 1) ↔ p = 5 := by
  constructor
  · -- Assume (Nat.Prime (4 * p ^ 2 + 1) ∧ Nat.Prime (6 * p ^ 2 + 1)), prove p = 5
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h3 : p <= 5
    · -- If p ≤ 5 and p is prime, then p can be 2, 3, or 5
      interval_cases p <;> norm_num at hp h1 h2 ⊢ <;> try { trivial }
    · -- Assume p > 5
      have h4 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 ∨ p % 5 = 0 := by 
        omega
      rcases h4 with (h | h | h | h | h)
      · -- p ≡ 1 mod 5
        have h5 : (4 * p ^ 2 + 1) % 5 = 0 := by
          have : p % 5 = 1 := h
          have hp2 : p ^ 2 % 5 = 1 := by
            norm_num [Nat.pow_mod, this]
          omega
        have h6 : ¬ Nat.Prime (4 * p ^ 2 + 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (4 * p ^ 2 + 1) by omega)
          all_goals 
            nlinarith
            <;> nlinarith
        contradiction
      · -- p ≡ 2 mod 5
        have h5 : (6 * p ^ 2 + 1) % 5 = 0 := by
          have : p % 5 = 2 := h
          have hp2 : p ^ 2 % 5 = 4 := by
            norm_num [Nat.pow_mod, this]
          omega
        have h6 : ¬ Nat.Prime (6 * p ^ 2 + 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (6 * p ^ 2 + 1) by omega)
          all_goals 
            nlinarith
            <;> nlinarith
        contradiction
      · -- p ≡ 3 mod 5
        have h5 : (6 * p ^ 2 + 1) % 5 = 0 := by
          have : p % 5 = 3 := h
          have hp2 : p ^ 2 % 5 = 4 := by
            norm_num [Nat.pow_mod, this]
          omega
        have h6 : ¬ Nat.Prime (6 * p ^ 2 + 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (6 * p ^ 2 + 1) by omega)
          all_goals 
            nlinarith
            <;> nlinarith
        contradiction
      · -- p ≡ 4 mod 5
        have h5 : (4 * p ^ 2 + 1) % 5 = 0 := by
          have : p % 5 = 4 := h
          have hp2 : p ^ 2 % 5 = 1 := by
            norm_num [Nat.pow_mod, this]
          omega
        have h6 : ¬ Nat.Prime (4 * p ^ 2 + 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (4 * p ^ 2 + 1) by omega)
          all_goals 
            nlinarith
            <;> nlinarith
        contradiction
      · -- p ≡ 0 mod 5
        have h5 : p % 5 = 0 := by
          omega
        have h6 : ¬ Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega)
          all_goals 
            nlinarith
            <;> nlinarith
        contradiction
  · -- Assume p = 5, prove Nat.Prime (4 * p ^ 2 + 1) ∧ Nat.Prime (6 * p ^ 2 + 1)
    intro h
    rw [h]
    constructor
    · -- Show that 4 * 5^2 + 1 is prime
      norm_num
    · -- Show that 6 * 5^2 + 1 is prime
      norm_num