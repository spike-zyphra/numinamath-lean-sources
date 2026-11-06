import Mathlib

theorem number_theory_259617 {p : ℕ} (hp : p.Prime) :
    (p ^ 2 + 8).Prime ↔ p = 3 := by
  constructor
  · -- Assume (p ^ 2 + 8).Prime, prove p = 3
    intro h
    have h2 : p ≥ 2 := Nat.Prime.two_le hp
    by_cases h3 : p = 2
    · -- p = 2
      rw [h3] at h
      norm_num at h
    · -- p ≠ 2
      have h4 : p ≥ 3 := by
        by_contra h'
        push_neg at h'
        have h5 : p = 2 := by
          interval_cases p <;> tauto
        contradiction
      by_cases h5 : p % 3 = 0
      · -- p % 3 = 0
        have h6 : p = 3 := by
          have h7 : p ≥ 3 := h4
          have h8 : p ≤ 3 := by
            by_contra h'
            push_neg at h'
            have h9 : ¬ p.Prime := by
              apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
              all_goals omega
            contradiction
          linarith
        exact h6
      · -- p % 3 ≠ 0
        have h6 : p % 3 = 1 ∨ p % 3 = 2 := by
          omega
        rcases h6 with (h6 | h6)
        · -- p % 3 = 1
          have h7 : (p ^ 2) % 3 = 1 := by
            simp [Nat.pow_mod, h6]
          have h8 : (p ^ 2 + 8) % 3 = 0 := by
            omega
          have h9 : (p ^ 2 + 8) > 3 := by
            nlinarith [show p ≥ 3 by omega]
          have h10 : ¬ (p ^ 2 + 8).Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p ^ 2 + 8) by omega)
            all_goals nlinarith [show p ≥ 3 by omega]
          contradiction
          all_goals omega
        · -- p % 3 = 2
          have h7 : (p ^ 2) % 3 = 1 := by
            simp [Nat.pow_mod, h6]
          have h8 : (p ^ 2 + 8) % 3 = 0 := by
            omega
          have h9 : (p ^ 2 + 8) > 3 := by
            nlinarith [show p ≥ 3 by omega]
          have h10 : ¬ (p ^ 2 + 8).Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p ^ 2 + 8) by omega)
            all_goals nlinarith [show p ≥ 3 by omega]
          contradiction
          all_goals omega
  · -- Assume p = 3, prove (p ^ 2 + 8).Prime
    intro h
    rw [h]
    norm_num