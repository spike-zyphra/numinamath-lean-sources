import Mathlib

theorem number_theory_12423 (p q : ℕ) (h₀ : p.Prime) (h₁ : q.Prime)
    (h₂ : (7 * p + q).Prime) (h₃ : (2 * q + 11).Prime) :
    p ^ q + q ^ p = 17 := by
  by_cases h4 : p > 2
  · -- p > 2, so p is odd
    have h5 : p % 2 = 1 := by
      by_contra h
      push_neg at h
      have h6 : p % 2 = 0 := by
        omega
      have h7 : p > 2 := by
        omega
      have h8 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
        all_goals linarith
      contradiction
    by_cases h4' : q % 2 = 1
    · -- q is odd
      have h6 : (7 * p + q) % 2 = 0 := by
        have hp1 : p % 2 = 1 := h5
        have hq1 : q % 2 = 1 := h4'
        omega
      have h7 : ¬ (7 * p + q).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (7 * p + q) by omega)
        all_goals
        have h8 : 7 * p + q > 2 := by
          have hp2 : p > 2 := h4
          have hq2 : q ≥ 3 := by
            by_contra h
            push_neg at h
            have h9 : q < 3 := by
              omega
            interval_cases q <;> norm_num at h₁ h4' <;> try tauto
          omega
        all_goals
        omega
      contradiction
    · -- q = 2
      have h8 : q = 2 := by
        have h9 : q % 2 = 0 := by
          omega
        by_cases h10 : q > 2
        · -- q > 2, not prime
          have h11 : ¬q.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
            all_goals
            omega
          contradiction
        · -- q ≤ 2
          interval_cases q <;> norm_num at h₁ h9 ⊢
          <;> try tauto
      rw [h8] at h₃
      norm_num at h₃
      all_goals try tauto
  · -- p ≤ 2
    have hp2 : p = 2 := by
      interval_cases p <;> norm_num at h₀ ⊢
      <;> try tauto
    have h9 : p = 2 := hp2
    by_cases h4' : q > 3
    · -- q > 3
      have h6 : q % 2 = 1 := by
        by_contra h
        push_neg at h
        have h10 : q % 2 = 0 := by
          omega
        have h11 : q > 3 := h4'
        have h12 : ¬q.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
          all_goals
          omega
        contradiction
      by_cases h7 : q % 3 = 1
      · -- q % 3 = 1
        have h8 : (7 * p + q) % 3 = 0 := by
          rw [show p = 2 by omega]
          omega
        have h9 : ¬ (7 * p + q).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (7 * p + q) by omega)
          all_goals
          -- goals to be proven
          have h10 : 7 * p + q > 3 := by
            omega
          all_goals
          omega
        contradiction
      by_cases h8 : q % 3 = 2
      · -- q % 3 = 2
        have h10 : (2 * q + 11) % 3 = 0 := by
          omega
        have h11 : ¬ (2 * q + 11).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (2 * q + 11) by omega)
          all_goals
          have h12 : 2 * q + 11 > 3 := by
            omega
          all_goals
          omega
        contradiction
      have h8' : q % 3 = 0 := by
        omega
      have h9 : ¬q.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega)
        all_goals
        have h10 : q > 3 := h4'
        omega
      contradiction
    · -- q ≤ 3
      interval_cases q <;> norm_num [h9] at h₁ h₂ h₃ ⊢
      <;> try { tauto }
      <;> norm_num
      <;> try { tauto }