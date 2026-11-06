import Mathlib

theorem number_theory_237687 (p : ℕ) (hp : Nat.Prime p) :
    Nat.Prime (p + 10) ∧ Nat.Prime (p + 14) ↔ p = 3 := by
  constructor
  · -- Assume Nat.Prime (p + 10) ∧ Nat.Prime (p + 14), prove p = 3
    intro h
    rcases h with ⟨h10, h14⟩
    by_cases h3 : p ≤ 3
    · interval_cases p <;> norm_num at hp h10 h14 ⊢ <;> try { tauto }
    · -- Assume p > 3, so p ≡ 1 or 2 (mod 3)
      have h4 : p > 3 := by
        by_contra h
        push_neg at h
        linarith
      have h5 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
        omega
      rcases h5 with (h5 | h5 | h5)
      · -- p ≡ 0 (mod 3)
        have h6 : p % 3 = 0 := by
          omega
        have h7 : ¬Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
          all_goals
            omega
        contradiction
      · -- p ≡ 1 (mod 3)
        have h8 : p % 3 = 1 := by
          omega
        have h9 : (p + 14) % 3 = 0 := by
          omega
        have h10 : ¬Nat.Prime (p + 14) := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 14) by omega)
          all_goals
            omega
        contradiction
      · -- p ≡ 2 (mod 3)
        have h11 : p % 3 = 2 := by
          omega
        have h12 : (p + 10) % 3 = 0 := by
          omega
        have h13 : ¬Nat.Prime (p + 10) := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 10) by omega)
          all_goals
            omega
        contradiction
  · -- Assume p = 3, prove Nat.Prime (p + 10) ∧ Nat.Prime (p + 14)
    intro hp2
    rw [hp2]
    constructor
    · -- Check that 3 + 10 = 13 is prime
      norm_num
    · -- Check that 3 + 14 = 17 is prime
      norm_num