import Mathlib

theorem number_theory_238646 (p : ℕ) (hp : Nat.Prime p) :
    Nat.Prime (p^2 + 2 * p + 11) ∧ Nat.Prime (p^2 + p + 13) ↔ p = 2 := by
  constructor
  · -- Forward: if both expressions are prime, then p = 2
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h3 : p > 2
    · -- p > 2
      have h4 : p % 2 = 1 := by
        by_contra h
        push_neg at h
        have : p % 2 = 0 := by omega
        have : p > 2 := by linarith
        have : ¬Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
          all_goals linarith
        contradiction
      have h5 : (p ^ 2 + 2 * p + 11) % 2 = 0 := by
        have h6 : p % 2 = 1 := h4
        have h7 : p % 2 = 1 := h6
        have h8 : p ^ 2 % 2 = 1 := by
          simp [Nat.pow_mod, h6]
        have h9 : (2 * p) % 2 = 0 := by
          simp [Nat.mul_mod, h6]
        omega
      have h6 : ¬Nat.Prime (p ^ 2 + 2 * p + 11) := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (p ^ 2 + 2 * p + 11) by omega)
        all_goals
        nlinarith [show p ≥ 3 by omega, h5]
      contradiction
    · -- p ≤ 2
      have : p ≤ 2 := by linarith
      interval_cases p <;> norm_num at hp h1 h2 ⊢ <;> tauto
  · -- Backward: if p = 2, then both expressions are prime
    intro hp_eq
    rw [hp_eq]
    constructor
    · norm_num
    · norm_num