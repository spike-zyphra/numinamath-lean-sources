import Mathlib

theorem number_theory_153615 (p : ℕ) (hp : p.Prime) :
    (20 * p^2 + 1).Prime ↔ p = 3 := by
  constructor
  · -- Forward: if 20 * p^2 + 1 is prime, then p = 3
    intro h
    by_cases h2 : p ≤ 3
    · -- p ≤ 3
      interval_cases p <;> norm_num at h hp ⊢ <;> tauto
    · -- p > 3
      have h3 : p % 3 = 1 ∨ p % 3 = 2 := by
        by_contra h'
        push_neg at h'
        have h4 : p % 3 = 0 := by omega
        have h5 : p > 3 := by omega
        have h6 : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
          all_goals omega
        contradiction
      have h4 : (20 * p^2 + 1 : ℕ) % 3 = 0 := by
        rcases h3 with (h3 | h3)
        · -- p % 3 = 1
          have h1 : p % 3 = 1 := h3
          have h1' : p^2 % 3 = 1 := by
            simp [Nat.pow_mod, h1]
          omega
        · -- p % 3 = 2
          have h1 : p % 3 = 2 := h3
          have h1' : p^2 % 3 = 1 := by
            simp [Nat.pow_mod, h1]
          omega
      have h5 : ¬ (20 * p^2 + 1 : ℕ).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (20 * p^2 + 1) by omega)
        all_goals
        nlinarith [show p ≥ 1 by linarith]
        all_goals
        nlinarith
      contradiction
  · -- Backward: if p = 3, then 20 * p^2 + 1 is prime
    intro h_eq3
    rw [h_eq3]
    norm_num