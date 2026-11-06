import Mathlib

theorem number_theory_310698 (p : ℕ) (hp : p.Prime) :
    Nat.Prime (8 * p^2 + 1) ↔ p = 3 := by
  constructor
  · -- Assume Nat.Prime (8 * p^2 + 1), prove p = 3
    intro h
    by_cases h1 : p ≤ 3
    · interval_cases p <;> norm_num at hp h ⊢ <;> trivial
    · -- p > 3
      push_neg at h1
      have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
        have h3 : p % 3 ≠ 0 := by
          by_contra h4
          have h5 : p > 3 := by linarith
          have h6 : ¬p.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show (3 : ℕ) ∣ p by omega)
            all_goals nlinarith
          contradiction
        omega
      cases h2 with
      | inl h2 =>
        have h3 : (8 * p^2 + 1) % 3 = 0 := by
          have hp1 : p % 3 = 1 := h2
          have h4 : p^2 % 3 = 1 := by
            have h5 : p % 3 = 1 := h2
            norm_num [Nat.pow_mod, h5]
          omega
        have h4 : ¬Nat.Prime (8 * p^2 + 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show (3 : ℕ) ∣ (8 * p^2 + 1) by omega)
          all_goals
            have h5 : p ≥ 4 := by nlinarith
            nlinarith
        contradiction
      | inr h2 =>
        have h3 : (8 * p^2 + 1) % 3 = 0 := by
          have hp1 : p % 3 = 2 := h2
          have h4 : p^2 % 3 = 1 := by
            have h5 : p % 3 = 2 := h2
            norm_num [Nat.pow_mod, h5]
          omega
        have h4 : ¬Nat.Prime (8 * p^2 + 1) := by
          apply Nat.not_prime_of_dvd_of_lt (show (3 : ℕ) ∣ (8 * p^2 + 1) by omega)
          all_goals
            have h5 : p ≥ 4 := by nlinarith
            nlinarith
        contradiction
  · -- Assume p = 3, prove Nat.Prime (8 * p^2 + 1)
    intro hp_eq
    rw [hp_eq]
    norm_num