import Mathlib

theorem number_theory_4513 {a b c : ℤ}
    (hab : a.gcd b = 1) (hc : c ∣ (a + b)) : c.gcd a = 1 ∧ c.gcd b = 1 := by
  constructor
  · -- Show that $\gcd(c, a) = 1$
    have h1 : (c.gcd a : ℤ) ∣ c := by
      apply Int.gcd_dvd_left
    have h2 : (c.gcd a : ℤ) ∣ a := by
      apply Int.gcd_dvd_right
    have h3 : (c.gcd a : ℤ) ∣ b := by
      have h4 : (c.gcd a : ℤ) ∣ (a + b) := by
        exact dvd_trans (Int.gcd_dvd_left) hc
      have h5 : (c.gcd a : ℤ) ∣ b := by
        have h6 : (c.gcd a : ℤ) ∣ (a + b - a) := by
          apply Dvd.dvd.sub
          · exact h4
          · exact h2
        have h7 : (a + b - a : ℤ) = b := by
          omega
        rw [h7] at h6
        exact h6
      exact h5
    have h8 : (c.gcd a : ℤ) ∣ (a.gcd b : ℤ) := by
      apply Int.dvd_gcd
      · exact h2
      · exact h3
    rw [show (a.gcd b : ℤ) = 1 by
      omega
    ] at h8
    have h10 : (c.gcd a : ℤ) ≤ 1 := by
      exact Int.le_of_dvd (by norm_num) h8
    have h11 : c.gcd a = 1 := by 
      -- Note: c.gcd a is a natural number 
      have h11a : c.gcd a ≤ 1 := by
        omega -- need to work on ℕ, not ℤ
      have h11b : c.gcd a ≥ 0 := by
        -- gcd always non-negative
        have h : c.gcd a ≥ 0 := by
          apply Nat.zero_le 
        omega
      have h11c : c.gcd a = 1 := by
        have h12 : (c.gcd a : ℤ) ∣ 1 := h8
        have h13 : (c.gcd a : ℤ) ≤ 1 := h10
        have h14 : (c.gcd a : ℤ) ≥ 0 := by 
          omega 
        have h15 : (c.gcd a : ℤ) = 1 := by
          have h22 : (c.gcd a : ℤ) ≤ 1 := h10
          have h23 : (c.gcd a : ℤ) ≥ 0 := h14
          have h24 : (c.gcd a : ℤ) = 1 := by
            have h18 : (c.gcd a : ℤ) ∣ 1 := h8
            have : (c.gcd a : ℤ) = 1 := by
              have h26 : (c.gcd a : ℤ) ≤ 1 := by
                omega 
              have h27 : (c.gcd a : ℤ) ≥ 0 := by
                omega 
              interval_cases h : (c.gcd a : ℤ) <;> try { tauto }
              all_goals try { 
                norm_num at h18 
                all_goals tauto 
              }
              all_goals try { omega }
            assumption
          assumption
        have h17 : (c.gcd a : ℤ) = 1 := h15
        norm_cast at h17 ⊢
      assumption
    exact_mod_cast h11
  · -- Show that $\gcd(c, b) = 1$
    have h1 : (c.gcd b : ℤ) ∣ c := by
      apply Int.gcd_dvd_left
    have h2 : (c.gcd b : ℤ) ∣ b := by
      apply Int.gcd_dvd_right
    have h3 : (c.gcd b : ℤ) ∣ a := by
      have h4 : (c.gcd b : ℤ) ∣ (a + b) := by
        exact dvd_trans (Int.gcd_dvd_left) hc
      have h5 : (c.gcd b : ℤ) ∣ a := by
        have h6 : (c.gcd b : ℤ) ∣ (a + b - b) := by
          apply Dvd.dvd.sub 
          · exact h4
          · exact h2
        have h7 : (a + b - b : ℤ) = a := by
          omega
        rw [h7] at h6
        exact h6
      exact h5
    have h8 : (c.gcd b : ℤ) ∣ (a.gcd b : ℤ) := by
      apply Int.dvd_gcd
      · exact h3
      · exact h2
    rw [show (a.gcd b : ℤ) = 1 by 
      omega
    ] at h8
    have h10 : (c.gcd b : ℤ) ≤ 1 := by
      exact Int.le_of_dvd (by norm_num) h8
    have h11 : c.gcd b = 1 := by
      -- Note: c.gcd b is a natural number
      have h11a : c.gcd b ≤ 1 := by
        omega -- need to work on ℕ, not ℤ
      have h11b : c.gcd b ≥ 0 := by
        -- gcd always non-negative
        have h : c.gcd b ≥ 0 := by
          apply Nat.zero_le 
        omega
      have h11c : c.gcd b = 1 := by
        have h12 : (c.gcd b : ℤ) ∣ 1 := h8
        have h13 : (c.gcd b : ℤ) ≤ 1 := h10
        have h14 : (c.gcd b : ℤ) ≥ 0 := by
          omega 
        have h15 : (c.gcd b : ℤ) = 1 := by
          have h22 : (c.gcd b : ℤ) ∣ 1 := h8
          have h23 : (c.gcd b : ℤ) ≤ 1 := h10
          have h24 : (c.gcd b : ℤ) ≥ 0 := h14
          have h25 : (c.gcd b : ℤ) = 1 := by
            have h18 : (c.gcd b : ℤ) ∣ 1 := h8
            have : (c.gcd b : ℤ) = 1 := by
              have h26 : (c.gcd b : ℤ) ≤ 1 := by
                omega 
              have h27 : (c.gcd b : ℤ) ≥ 0 := by
                omega 
              interval_cases h : (c.gcd b : ℤ) <;> try { tauto }
              all_goals try { 
                norm_num at h18 
                all_goals tauto 
              }
              all_goals try { omega }
            assumption
          assumption
        have h17 : (c.gcd b : ℤ) = 1 := h15
        norm_cast at h17 ⊢
      assumption
    exact_mod_cast h11