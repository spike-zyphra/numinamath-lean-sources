import Mathlib

theorem number_theory_90524 :
    {(p, q) | Nat.Prime p ∧ Nat.Prime q ∧ 7 * p * q ^ 2 + p = q ^ 3 + 43 * p ^ 3 + 1 } = { (2, 7) } := by
  ext ⟨p, q⟩
  simp [-one_div]
  constructor
  · -- Assume ⟨p, q⟩ is in the left side, prove it equals (2, 7)
    rintro ⟨hp, hq, heq⟩
    by_cases hp2 : p % 2 = 1
    · -- Assume p is odd, then q must be even
      by_cases hq2 : q % 2 = 0
      · -- Assume q is even, then q must be 2
        have hq_eq_2 : q = 2 := by
          by_cases hq1 : q > 2
          · -- Assume q > 2, then it's an even prime greater than 2, which is impossible
            have : q % 2 = 0 := by exact hq2
            have h11 : q > 2 := hq1
            have h12 : q % 2 = 0 := by exact hq2
            have h13 : q > 2 := hq1
            -- Show contradiction
            have h14 : q ≠ 2 := by omega
            have h15 : q > 2 := hq1
            have h16 : ¬Nat.Prime q := by
              apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
              all_goals omega
            tauto
          interval_cases q <;> norm_num at *
        rw [hq_eq_2] at heq
        have h11 : p ≥ 2 := Nat.Prime.two_le hp
        nlinarith [sq_nonneg (p ^ 2 - 1 : ℤ), sq_nonneg (p - 1 : ℤ), Nat.Prime.two_le hp, sq_nonneg (p : ℤ)]
      · -- Assume q is odd, then q % 2 = 1
        have hq2' : q % 2 = 1 := by
          omega
        -- Now derive a contradiction
        -- Show that left side is even, right side is odd
        have h11 : (7 * p * q ^ 2 + p : ℕ) % 2 = 0 := by
          have hp1 : p % 2 = 1 := hp2
          have hq1 : q % 2 = 1 := hq2'
          have h12 : (q ^ 2) % 2 = 1 := by
            have hq1' : q % 2 = 1 := hq1
            have : q % 2 = 1 := hq1'
            have h4 : (q ^ 2 : ℕ) % 2 = 1 := by
              simp [Nat.pow_mod, hq1']
            assumption
          calc
            (7 * p * q ^ 2 + p : ℕ) % 2 = ((7 * p * q ^ 2) + p) % 2 := by ring_nf
            _ = ((7 * p * q ^ 2) % 2 + (p % 2)) % 2 := by simp [Nat.add_mod]
            _ = (1 + 1) % 2 := by
              have h31 : (7 * p * q ^ 2) % 2 = 1 := by
                simp [Nat.mul_mod, hp1, hq1, h12]
              have h32 : p % 2 = 1 := by exact hp1
              simp [h31, h32]
            _ = (2) % 2 := by norm_num
            _ = 0 := by norm_num
        have h4 : (q ^ 3 + 43 * p ^ 3 + 1 : ℕ) % 2 = 1 := by
          have hp1 : p % 2 = 1 := hp2
          have hq1 : q % 2 = 1 := hq2'
          have h11 : (q ^ 3) % 2 = 1 := by
            have hq1' : q % 2 = 1 := hq1
            simp [Nat.pow_mod, hq1']
          have h12 : (43 * p ^ 3) % 2 = 1 := by
            have hp1' : p % 2 = 1 := hp1
            have h43 : (43 : ℕ) % 2 = 1 := by norm_num
            have hp3 : (p ^ 3) % 2 = 1 := by
              simp [Nat.pow_mod, hp1']
            omega
          omega
        omega
    · -- Assume p is even, then p must be 2
      have hp2' : p % 2 = 0 := by
        omega
      have hp_eq_2 : p = 2 := by
        by_cases hp1 : p > 2
        · -- Assume p > 2, then even prime greater 2 than is impossible
          have h11 : p % 2 = 0 := by exact hp2'
          have h12 : p > 2 := hp1
          have h13 : ¬Nat.Prime p := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
            all_goals omega
          tauto
        interval_cases p <;> norm_num at *
      rw [hp_eq_2] at heq
      have h11 : q ≤ 43 := by
        by_contra h
        push_neg at h
        nlinarith [sq_nonneg (q : ℤ), sq_nonneg ((q - 7 : ℤ)), sq_nonneg ((q - 43 : ℤ)), pow_pos (show (0 : ℕ) < 2 by norm_num) 3]
      interval_cases q <;> norm_num at heq hq <;> tauto
  · -- Show that (2, 7) is in the set
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    all_goals norm_num