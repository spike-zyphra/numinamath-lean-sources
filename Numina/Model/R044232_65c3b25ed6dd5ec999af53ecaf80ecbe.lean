import Mathlib

theorem number_theory_294991 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h2p : (2 * p + q).Prime) (h2q : (p + 2 * q).Prime) (hsum : (p + q - 18).Prime) :
    (p = 3 ∧ q = 17) ∨ (p = 17 ∧ q = 3) := by
  by_cases h19 : p + q > 18
  · -- If p + q > 18, then p + q - 18 ≥ 1
    have h1 : p + q ≥ 19 := by omega
    have h3 : (p + q - 18) % 2 = 0 ∨ (p + q - 18) % 2 = 1 := by omega
    rcases h3 with (h3 | h3)
    · -- If p + q - 18 is even
      have h4 : (p + q - 18) % 2 = 0 := h3
      have h5 : (p + q - 18) = 2 := by
        by_cases h6 : (p + q - 18) > 2
        · -- If p + q - 18 > 2
          have h7 : ¬ (p + q - 18).Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (p + q - 18) by omega)
            all_goals omega
          contradiction
        · -- If p + q - 18 ≤ 2
          have h8 : (p + q - 18) ≤ 2 := by omega
          interval_cases h9 : (p + q - 18) <;> try tauto
      have h10 : p + q = 20 := by
        omega
      have h11 : p ≤ 20 := by omega
      have h12 : q = 20 - p := by omega
      interval_cases p <;> norm_num [h12] at hp hq h2p h2q hsum ⊢
    · -- If p + q - 18 is odd
      have h13 : (p + q - 18) % 2 = 1 := h3
      have h14 : p % 2 = 0 ∨ p % 2 = 1 := by omega
      rcases h14 with (h14 | h14)
      · -- If p is even
        have h16 : p % 2 = 0 := h14
        have h17 : p = 2 := by
          by_cases h17 : p > 2
          · -- If p > 2
            have h18 : ¬ p.Prime := by
              apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
              all_goals omega
            contradiction
          · -- If p ≤ 2
            interval_cases p <;> try tauto
        rw [show p = 2 by omega] at h2q
        have h30 : (2 + 2 * q) % 2 = 0 := by omega
        have h31 : (2 + 2 * q) = 2 := by
          by_cases h6 : (2 + 2 * q) > 2
          · -- If 2 + 2 * q > 2
            have h7 : ¬ (2 + 2 * q).Prime := by
              apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (2 + 2 * q) by omega)
              all_goals omega
            contradiction
          · -- If 2 + 2 * q ≤ 2
            have h8 : (2 + 2 * q) ≤ 2 := by omega
            have h9 : (2 + 2 * q) = 2 := by
              interval_cases h9 : (2 + 2 * q) <;> try tauto
            exact h9
        have h32 : q = 0 := by omega
        have h33 : ¬q.Prime := by
          rw [h32]
          norm_num
        contradiction
      · -- If p is odd
        have h19 : p % 2 = 1 := h14
        have h20 : q % 2 = 0 ∨ q % 2 = 1 := by omega
        rcases h20 with (h20 | h20)
        · -- If q is even
          have h21 : q % 2 = 0 := h20
          have h22 : q = 2 := by
            by_cases h22 : q > 2
            · -- If q > 2
              have h23 : ¬ q.Prime := by
                apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
                all_goals omega
              contradiction
            · -- If q ≤ 2
              interval_cases q <;> try tauto
          rw [show q = 2 by omega] at h2p
          have h30 : (2 * p + 2) % 2 = 0 := by omega
          have h31 : (2 * p + 2) = 2 := by
            by_cases h6 : (2 * p + 2) > 2
            · -- If 2 * p + 2 > 2
              have h7 : ¬ (2 * p + 2).Prime := by
                apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (2 * p + 2) by omega)
                all_goals omega
              contradiction
            · -- If 2 * p + 2 ≤ 2
              have h8 : (2 * p + 2) ≤ 2 := by omega
              have h9 : (2 * p + 2) = 2 := by
                interval_cases h9 : (2 * p + 2) <;> try tauto
              exact h9
          have h32 : p = 0 := by omega
          have h33 : ¬p.Prime := by
            rw [h32]
            norm_num
          contradiction
        · -- If q is odd
          have h24 : q % 2 = 1 := h20
          have h25 : (p + q) % 2 = 0 := by 
            omega
          have h26 : (p + q - 18) % 2 = 0 := by 
            omega
          omega
  · -- If p + q ≤ 18
    have h10 : p ≤ 18 := by
      omega
    have h11 : q ≤ 18 := by
      omega
    interval_cases p <;> interval_cases q
    <;> norm_num at hp hq h2p h2q hsum ⊢