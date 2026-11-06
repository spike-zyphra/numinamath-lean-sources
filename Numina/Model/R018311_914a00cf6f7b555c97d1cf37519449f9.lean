import Mathlib

theorem number_theory_137230 (n : ℕ) (hn : n > 0) :
    Nat.Prime (n + 1) ∧ Nat.Prime (n + 3) ∧ Nat.Prime (n + 7) ∧
    Nat.Prime (n + 9) ∧ Nat.Prime (n + 13) ∧ Nat.Prime (n + 15) ↔ n = 4 := by
  constructor
  · -- Assume all the numbers are prime, prove n = 4
    intro h
    rcases h with ⟨h1, h3, h7, h9, h13, h15⟩
    by_cases h3 : n ≤ 4
    · interval_cases n <;> norm_num at h1 h3 h7 h9 h13 h15 ⊢ <;> tauto
    · -- n > 4
      push_neg at h3
      have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
        omega
      rcases h4 with (h5 | h5 | h5 | h5 | h5)
      · -- n % 5 = 0
        have h5 : (n + 15) % 5 = 0 := by
          omega
        have h6 : ¬ Nat.Prime (n + 15) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (n + 15) by omega)
          all_goals omega
        contradiction
      · -- n % 5 = 1
        have h5 : (n + 9) % 5 = 0 := by
          omega
        have h6 : ¬ Nat.Prime (n + 9) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (n + 9) by omega)
          all_goals omega
        contradiction
      · -- n % 5 = 2
        have h5 : (n + 3) % 5 = 0 := by
          omega
        have h6 : ¬ Nat.Prime (n + 3) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (n + 3) by omega)
          all_goals omega
        contradiction
      · -- n % 5 = 3
        have h5 : (n + 7) % 5 = 0 := by
          omega
        have h6 : ¬ Nat.Prime (n + 7) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (n + 7) by omega)
          all_goals omega
        contradiction
      · -- n % 5 = 4
        have h5 : (n + 1) % 5 = 0 := by 
          omega
        have h6 : ¬ Nat.Prime (n + 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (n + 1) by omega)
          all_goals omega
        contradiction
  · -- Backward direction
    intro h
    rw [h]
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num