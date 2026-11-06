import Mathlib

theorem number_theory_6474
    (p q : ℕ)
    (h₀ : p.Prime)
    (h₁ : q.Prime)
    (h₂ : p * (p - 1) = q * (q + 1)) :
    p = 3 ∧ q = 2 := by
  have h3 : p > 1 := h₀.one_lt
  have h4 : q > 1 := h₁.one_lt
  by_cases h5 : p ≤ q + 1
  · -- Assume p ≤ q + 1, then since p = q + 1, we have p = q + 1
    by_cases h6 : p = q + 1
    · -- Assume p = q + 1
      have h7 : p = q + 1 := h6
      rw [h7] at h₂
      by_cases h8 : q < 3
      · -- Assume q < 3, then q must 2
        have h9 : q = 2 := by
          by_cases h10 : q > 1
          · -- Assume q > 1, since q < 3, q = 2
            have h11 : q = 2 := by
              linarith
            exact h11
          · -- Assume q ≤ 1, but q is prime, so contradiction
            have h4 : q > 1 := h₁.one_lt
            omega
        have h10 : p = 3 := by
          rw [h9] at h7
          omega
        constructor
        · exact h10
        · exact h9
      · -- Assume q ≥ 3
        push_neg at h8
        have h5 : q % 2 = 0 ∨ q % 2 = 1 := by omega
        rcases h5 with (h5 | h5)
        · -- Assume q % 2 = 0
          have h8 : q > 2 := by omega
          have h9 : ¬q.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
            all_goals omega
          contradiction
        · -- Assume q % 2 = 1
          have h10 : p % 2 = 0 := by
            omega
          have h11 : p > 2 := by
            omega
          have h12 : ¬p.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
            all_goals omega
          contradiction
    · -- Assume p ≠ q + 1, since p ≤ q + 1, so p < q + 1, contradiction
      push_neg at h6
      have h7 : p < q + 1 := by
        omega
      have h8 : p ≤ q := by
        omega
      have h9 : p * (p - 1) < q * (q + 1) := by
        have h10 : p ≤ q := h8
        have h11 : p - 1 < q + 1 := by
          omega
        have h12 : p * (p - 1) < q * (q + 1) := by
          nlinarith [show q ≥ 1 by nlinarith]
        nlinarith
      nlinarith
  · -- Assume p > q + 1, contradiction with the equation
    push_neg at h5
    have h6 : p ≥ q + 2 := by omega
    have h7 : p * (p - 1) > q * (q + 1) := by
      have h8 : p ≥ q + 2 := h6
      have h9 : p - 1 ≥ q + 1 := by
        omega
      nlinarith [show q ≥ 1 by nlinarith]
    nlinarith