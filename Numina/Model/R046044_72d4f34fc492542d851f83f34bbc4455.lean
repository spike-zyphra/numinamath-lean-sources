import Mathlib

theorem number_theory_150672 (p : ℕ) (hp : Odd p) :
    Nat.Prime p ∧ Nat.Prime (p + 2) ∧ Nat.Prime (p + 4) ↔ (p = 3 ∧ p + 2 = 5 ∧ p + 4 = 7) := by
  constructor
  · -- Forward implication: if p, p+2, p+4 are Nat.Prime
    intro h
    rcases h with ⟨h1, h2, h3⟩

    have h4 : p ≤ 7 := by
      by_contra h5
      push_neg at h5
      have h5 : p > 7 := by linarith
      have h5' : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
        omega
      rcases h5' with (h | h | h)
      · -- If p % 3 = 0
        have h6 : ¬ Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
          all_goals omega
        contradiction
      · -- If p % 3 = 1
        have h8 : (p + 2) % 3 = 0 := by
          omega
        have h9 : ¬ Nat.Prime (p + 2) := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 2) by omega)
          all_goals omega
        contradiction
      · -- If p % 3 = 2
        have h8 : (p + 4) % 3 = 0 := by
          omega
        have h9 : ¬ Nat.Prime (p + 4) := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 4) by omega)
          all_goals omega
        contradiction

    interval_cases p <;> norm_num at h1 h2 h3 <;> tauto
  · -- Backward implication: if p = 3, then p, p+2, p+4 are all prime
    rintro ⟨h1, h2, h3⟩
    rw [h1] at *
    constructor
    · -- Nat.Prime 3
      norm_num
    constructor
    · -- Nat.Prime 5
      norm_num
    · -- Nat.Prime 7
      norm_num