import Mathlib

theorem number_theory_130580 (p : ℕ) (hp : Nat.Prime p) :
    Nat.Prime (p + 28) ∧ Nat.Prime (p + 56) ↔ p = 3 := by
  constructor
  · -- Forward direction: Assume Nat.Prime (p + 28) ∧ Nat.Prime (p + 56), prove p = 3
    rintro ⟨h1, h2⟩
    by_cases h3 : p ≤ 3
    · -- Case: p ≤ 3
      interval_cases p <;> norm_num at hp h1 h2 ⊢ <;> tauto
    · -- Case: p > 3
      push_neg at h3
      have h4 : p % 3 = 1 ∨ p % 3 = 2 := by
        have h5 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
          omega
        rcases h5 with (h5 | h5 | h5)
        · -- Case: p % 3 = 0
          have h6 : p % 3 = 0 := by omega
          have h7 : 3 ∣ p := by
            exact Nat.dvd_of_mod_eq_zero h6
          have h8 : p ≠ 3 := by linarith
          have h9 : ¬Nat.Prime p := by
            apply Nat.not_prime_of_dvd_of_lt h7
            all_goals linarith
          contradiction
        · -- Case: p % 3 = 1
          left
          omega
        · -- Case: p % 3 = 2
          right
          omega
      rcases h4 with (h4 | h4)
      · -- Case: p % 3 = 1
        have h5 : (p + 56) % 3 = 0 := by
          omega
        have h6 : ¬Nat.Prime (p + 56) := by
          have h7 : 3 ∣ (p + 56) := by
            exact Nat.dvd_of_mod_eq_zero h5
          have h8 : 2 < 3 := by norm_num
          have h9 : 3 < p + 56 := by
            omega
          apply Nat.not_prime_of_dvd_of_lt h7 (by norm_num) h9
        contradiction
      · -- Case: p % 3 = 2
        have h5 : (p + 28) % 3 = 0 := by
          omega
        have h6 : ¬Nat.Prime (p + 28) := by
          have h7 : 3 ∣ (p + 28) := by
            exact Nat.dvd_of_mod_eq_zero h5
          have h8 : 2 < 3 := by norm_num
          have h9 : 3 < p + 28 := by
            omega
          apply Nat.not_prime_of_dvd_of_lt h7 (by norm_num) h9
        contradiction
  · -- Backward direction: Assume p = 3, prove Nat.Prime (p + 28) ∧ Nat.Prime (p + 56)
    intro h
    rw [h]
    constructor
    · norm_num
    · norm_num