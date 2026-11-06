import Mathlib

theorem number_theory_285509 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : q^5 - 2 * p^2 = 1) : p + q = 14 := by
  have h1 : q^5 = 2 * p^2 + 1 := by 
    omega
  by_cases h2 : q ≤ 3
  · -- q ≤ 3
    have : q = 2 ∨ q = 3 := by 
      interval_cases q <;> norm_num at hq 
      <;> tauto
    rcases this with (hq2 | hq3)
    · -- q = 2
      rw [hq2] at h1
      have h2 : 2^5 = 2 * p^2 + 1 := h1
      norm_num at h2
      have hp2 : p ≤ 3 := by
        nlinarith
      interval_cases p <;> norm_num at hp h2 
      all_goals contradiction
    · -- q = 3
      rw [hq3] at h1
      have h3 : 3^5 = 2 * p^2 + 1 := h1
      have hp_eq : p^2 = 121 := by 
        nlinarith
      have hp11 : p = 11 := by 
        nlinarith
      omega
  · -- q > 3
    push_neg at h2
    have h3 : q % 3 = 1 ∨ q % 3 = 2 := by 
      by_contra h4
      push_neg at h4
      have h40 : q % 3 = 0 := by omega
      have h41 : q > 3 := by omega
      have h42 : q ≠ 3 := by omega
      have h43 : ¬q.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega)
        all_goals omega
      contradiction
    have h4 : q ^ 5 % 3 = q % 3 := by
      have h1 : q % 3 = 1 ∨ q % 3 = 2 := h3
      rcases h1 with (h1 | h1)
      · 
        simp [h1, Nat.pow_mod, Nat.mul_mod]
      · 
        simp [h1, Nat.pow_mod, Nat.mul_mod]
    have h5 : (2 * p^2 + 1) % 3 = q ^ 5 % 3 := by
      omega
    rw [h4] at h5
    have h6 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by 
      omega
    rcases h3 with (h3 | h3)
    · -- q ≡ 1 (mod 3)
      -- h5 states (2 * p ^ 2 + 1) % 3 = 1
      have h7 : (2 * p ^ 2 + 1) % 3 = 1 := by 
        omega
      rcases h6 with (h6 | h6 | h6)
      · -- p % 3 = 0
        -- This implies p = 3
        have hp0 : p % 3 = 0 := h6
        have hp3 : p = 3 := by
          have hp8 : p % 3 = 0 := hp0
          have h6 : p ≤ 3 := by
            by_contra h6
            push_neg at h6
            have : p > 3 := by linarith
            have hp01 : ¬p.Prime := by 
              apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
              all_goals omega
            tauto
          interval_cases p <;> try tauto
        rw [hp3] at h1
        -- q^5 = 19
        have hq5 : q^5 = 19 := by
          omega
        have hq31 : q ≤ 2 := by
          by_contra h6
          push_neg at h6
          have h66 : q ≥ 3 := by omega
          have h67 : q^5 ≥ 243 := by
            have h68 : q ≥ 3 := h66
            have h1 : q^5 ≥ 3^5 := by
              apply Nat.pow_le_pow_of_le_left h68 5
            nlinarith
          nlinarith
        interval_cases q <;> norm_num at hq5 hq
      · -- p % 3 = 1
        -- This implies p^2 % 3 = 1
        have hp11 : p % 3 = 1 := h6
        have hp22 : p ^ 2 % 3 = 1 := by
          simp [hp11, Nat.pow_mod, Nat.mul_mod]
        omega -- Contradicts h7
      · -- p % 3 = 2
        -- This implies p^2 % 3 = 1
        have hp22 : p % 3 = 2 := h6
        have hp22 : p ^ 2 % 3 = 1 := by 
          simp [hp22, Nat.pow_mod, Nat.mul_mod]
        omega -- Contradicts h7
    · -- q ≡ 2 (mod 3)
      -- h5 states (2 * p ^ 2 + 1) % 3 = 2
      have h7 : (2 * p ^ 2 + 1) % 3 = 2 := by
        omega
      rcases h6 with (h6 | h6 | h6)
      · -- p % 3 = 0
        -- This implies p = 3, but then (2 * p^2 + 1) % 3 = 1, contradicting h7
        have hp0 : p % 3 = 0 := h6
        have hp3 : p = 3 := by
          have hp8 : p % 3 = 0 := hp0
          have h6 : p ≤ 3 := by
            by_contra h6
            push_neg at h6
            have : p > 3 := by linarith
            have hp01 : ¬p.Prime := by 
              apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
              all_goals omega
            tauto
          interval_cases p <;> try tauto
        rw [hp3] at h7 
        all_goals omega
      · -- p % 3 = 1
        -- This implies p^2 % 3 = 1
        have hp11 : p % 3 = 1 := h6
        have hp22 : p ^ 2 % 3 = 1 := by 
          simp [hp11, Nat.pow_mod, Nat.mul_mod]
        omega -- Contradicts h7
      · -- p % 3 = 2
        -- This implies p^2 % 3 = 1
        have hp22 : p % 3 = 2 := h6
        have hp22 : p ^ 2 % 3 = 1 := by 
          simp [hp22, Nat.pow_mod, Nat.mul_mod]
        omega -- Contradicts h7