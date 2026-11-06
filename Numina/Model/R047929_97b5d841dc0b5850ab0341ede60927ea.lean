import Mathlib

theorem number_theory_272236 (p : ℕ) (hp : Nat.Prime p) :
    Nat.Prime (4 * p ^ 2 + 1) ∧ Nat.Prime (6 * p ^ 2 + 1) ↔ p = 5 := by
  constructor
  · -- Forward: If Nat.Prime p and Nat.Prime (4p^2+1) and Nat.Prime (6p^2+1), then p = 5
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h3 : p ≤ 5
    · interval_cases p <;> norm_num at hp h1 h2 ⊢
      <;> try { trivial }
      <;> try { contradiction }
    · -- Assume p > 5
      have h4 : p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by 
        omega
      rcases h4 with (h | h | h | h | h)
      · -- p % 5 = 0
        have h5 : p % 5 = 0 := h
        have h6 : p ≠ 5 := by
          omega
        have h7 : ¬ Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega)
          all_goals omega
        contradiction
      · -- p % 5 = 1
        have h8 : (4 * p ^ 2 + 1) % 5 = 0 := by
          have h9 : p % 5 = 1 := h
          have h11 : p % 5 = 1 := h9
          have h12 : p ^ 2 % 5 = 1 := by
            norm_num [Nat.pow_mod, h11]
          omega
        have h5 : ¬ Nat.Prime (4 * p ^ 2 + 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (4 * p ^ 2 + 1) by omega)
          all_goals nlinarith [h8, show (4 * p ^ 2 + 1) > 5 by nlinarith]
        contradiction
      · -- p % 5 = 2
        have h8 : (6 * p ^ 2 + 1) % 5 = 0 := by
          have h9 : p % 5 = 2 := h
          have h11 : p % 5 = 2 := h9
          have h12 : p ^ 2 % 5 = 4 := by
            norm_num [Nat.pow_mod, h11]
          omega
        have h5 : ¬ Nat.Prime (6 * p ^ 2 + 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (6 * p ^ 2 + 1) by omega)
          all_goals nlinarith [h8, show (6 * p ^ 2 + 1) > 5 by nlinarith]
        contradiction
      · -- p % 5 = 3
        have h8 : (6 * p ^ 2 + 1) % 5 = 0 := by
          have h9 : p % 5 = 3 := h
          have h11 : p % 5 = 3 := h9
          have h12 : p ^ 2 % 5 = 4 := by
            norm_num [Nat.pow_mod, h11]
          omega
        have h5 : ¬ Nat.Prime (6 * p ^ 2 + 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (6 * p ^ 2 + 1) by omega)
          all_goals nlinarith [h8, show (6 * p ^ 2 + 1) > 5 by nlinarith]
        contradiction
      · -- p % 5 = 4
        have h8 : (4 * p ^ 2 + 1) % 5 = 0 := by
          have h9 : p % 5 = 4 := h
          have h11 : p % 5 = 4 := h9
          have h12 : p ^ 2 % 5 = 1 := by
            norm_num [Nat.pow_mod, h11]
          omega
        have h5 : ¬ Nat.Prime (4 * p ^ 2 + 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (4 * p ^ 2 + 1) by omega)
          all_goals nlinarith [h8, show (4 * p ^ 2 + 1) > 5 by nlinarith]
        contradiction
  · -- Backward: if p = 5, then Nat.Prime p and Nat.Prime (4p^2+1) and Nat.Prime (6p^2+1)
    intro h
    rw [h]
    constructor
    · norm_num
    · norm_num