import Mathlib

theorem number_theory_132838 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : ∃ r : ℕ, r.Prime ∧ r = 2^2 + p^2 + q^2) :
    (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2) := by
  rcases h with ⟨r, hr, hr_eq⟩

  have hp2 : p = 2 ∨ p % 2 = 1 := by 
    by_cases h1 : p ≤ 2
    · -- p ≤ 2
      interval_cases p <;> tauto
    · -- p > 2
      have h2 : p % 2 = 1 := by
        by_contra h
        push_neg at h
        have : p % 2 = 0 := by omega
        have : ¬p.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
          all_goals omega
        contradiction
      tauto

  have hq2 : q = 2 ∨ q % 2 = 1 := by
    by_cases h1 : q ≤ 2
    · -- q ≤ 2
      interval_cases q <;> tauto
    · -- q > 2
      have h2 : q % 2 = 1 := by
        by_contra h
        push_neg at h
        have : q % 2 = 0 := by omega
        have : ¬q.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
          all_goals omega
        contradiction
      tauto
  
  rcases hp2 with hp2 | hp2
  · -- p = 2 
    rcases hq2 with hq2 | hq2
    · -- q = 2 
      rw [hp2] at hr_eq
      rw [hq2] at hr_eq
      norm_num at hr_eq 
      rw [hr_eq] at hr
      norm_num at hr 
      all_goals tauto 
    · -- q % 2 = 1 
      have hr_eq' : r = 8 + q^2 := by 
        rw [hp2] at hr_eq
        nlinarith 
      by_cases h3 : q ≤ 7
      · -- q ≤ 7
        interval_cases q <;> norm_num [hp2] at *
        <;> norm_num [hr_eq'] at *
        <;> try { 
          tauto
        }
        <;> try { 
          exfalso
          <;> contradiction
        }
      · -- q > 7
        have h4 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
        rcases h4 with (h4 | h4 | h4)
        · -- q % 3 = 0 
          have h5 : q % 3 = 0 := h4
          have h6 : ¬q.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega)
            all_goals omega
          contradiction
        · -- q % 3 = 1
          have hr1 : r % 3 = 0 := by
            simp [hr_eq']
            have h7 : q % 3 = 1 := h4
            have h8 : q^2 % 3 = 1 := by
              simp [Nat.pow_mod, h7]
              <;> omega
            omega
          have h4 : r > 3 := by
            nlinarith [show q ≥ 4 by omega, sq_nonneg (q : ℕ)]
          have h5 : ¬r.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ r by omega)
            all_goals linarith
          contradiction
        · -- q % 3 = 2 
          have hr1 : r % 3 = 0 := by
            simp [hr_eq']
            have h7 : q % 3 = 2 := h4
            have h8 : q^2 % 3 = 1 := by
              simp [Nat.pow_mod, h7]
            omega
          have h4 : r > 3 := by
            nlinarith [show q ≥ 4 by omega, sq_nonneg (q : ℕ)]
          have h5 : ¬r.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ r by omega)
            all_goals linarith
          contradiction
  · -- p % 2 = 1 
    rcases hq2 with hq2 | hq2
    · -- q = 2 
      have hr_eq' : r = 8 + p^2 := by 
        rw [hq2] at hr_eq
        nlinarith 
      by_cases h3 : p ≤ 7
      · -- p ≤ 7
        interval_cases p <;> norm_num [hq2] at *
        <;> norm_num [hr_eq'] at *
        <;> try { 
          tauto
        }
        <;> try { 
          exfalso
          <;> contradiction
        }
      · -- p > 7
        have h4 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
        rcases h4 with (h4 | h4 | h4)
        · -- p % 3 = 0 
          have h5 : p % 3 = 0 := h4
          have h6 : ¬p.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
            all_goals omega
          contradiction
        · -- p % 3 = 1
          have hr1 : r % 3 = 0 := by
            simp [hr_eq']
            have h7 : p % 3 = 1 := h4
            have h8 : p^2 % 3 = 1 := by
              simp [Nat.pow_mod, h7]
            omega
          have h4 : r > 3 := by
            nlinarith [show p ≥ 4 by omega, sq_nonneg (p : ℕ)]
          have h5 : ¬r.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ r by omega)
            all_goals linarith
          contradiction
        · -- p % 3 = 2 
          have hr1 : r % 3 = 0 := by
            simp [hr_eq']
            have h7 : p % 3 = 2 := h4
            have h8 : p^2 % 3 = 1 := by
              simp [Nat.pow_mod, h7]
            omega
          have h4 : r > 3 := by
            nlinarith [show p ≥ 4 by omega, sq_nonneg (p : ℕ)]
          have h5 : ¬r.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ r by omega)
            all_goals linarith
          contradiction
    · -- q % 2 = 1 
      have hr_eq' : r = 4 + p^2 + q^2 := by 
        linarith [hr_eq]
      -- Now r must be even and greater than 2, contradiction 
      have h3 : r % 2 = 0 := by 
        simp [hr_eq']
        have h4 : p % 2 = 1 := hp2
        have h5 : q % 2 = 1 := hq2
        simp [Nat.add_mod, Nat.pow_mod, Nat.mul_mod, h4, h5]
        <;> omega 
      have h4 : r > 2 := by 
        nlinarith [show p ≥ 2 from Nat.Prime.two_le hp, show q ≥ 2 from Nat.Prime.two_le hq, sq_pos_of_pos (show (2 : ℕ) > 0 by norm_num), sq_nonneg (p : ℕ), sq_nonneg (q : ℕ), hp2, hq2, sq_nonneg (p * q : ℕ)]
      have h5 : ¬r.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ r by omega)
        all_goals linarith 
      contradiction