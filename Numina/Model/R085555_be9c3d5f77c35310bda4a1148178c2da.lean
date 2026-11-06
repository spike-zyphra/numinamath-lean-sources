import Mathlib

theorem number_theory_111304 (p : ℕ) (hp : Nat.Prime p) :
    Nat.Prime (p + 2) ∧ Nat.Prime (p + 4) ↔ p = 3 := by 
  constructor
  · -- Assume Nat.Prime (p + 2) ∧ Nat.Prime (p + 4), prove p = 3
    intro h
    rcases h with ⟨h2, h4⟩
    by_cases h3 : p ≤ 5
    · -- p ≤ 5
      interval_cases p <;> norm_num at hp h2 h4 <;> trivial
    · -- p > 5
      have h1 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
        omega
      rcases h1 with (h | h | h)
      · -- p % 3 = 0
        have h3 : ¬ Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
        contradiction
      · -- p % 3 = 1
        have h5 : (p + 2) % 3 = 0 := by omega
        have h6 : 3 ∣ (p + 2) := by omega
        have h7 : ¬ Nat.Prime (p + 2) := by
          apply Nat.not_prime_of_dvd_of_lt h6 (by omega) (by omega)
        contradiction
      · -- p % 3 = 2
        have h8 : (p + 4) % 3 = 0 := by omega
        have h9 : 3 ∣ (p + 4) := by omega
        have h10 : ¬ Nat.Prime (p + 4) := by
          apply Nat.not_prime_of_dvd_of_lt h9 (by omega) (by omega)
        contradiction
  · -- Assume p = 3, prove Nat.Prime (p + 2) ∧ Nat.Prime (p + 4)
    intro h_eq
    rw [h_eq]
    constructor
    · norm_num
    · norm_num