import Mathlib

open BigOperators

theorem Algebra_606043 (a b c : ℤ )(ha : a ≥ 1 )(hb : b ≥ 1) (hc :c ≥ 1)(h : a - b ≠ 0 ∧ b - c ≠ 0 ∧ c - a ≠ 0)(hab : a+b>c)(hbc:b+c>a)(hca:c+a>b) :
  abs (a * b^2 + b * c^2 + c * a^2 - a^2 * b - b^2 * c - c^2 * a) ≥ 2 := by
  have h4 : a * b^2 + b * c^2 + c * a^2 - a^2 * b - b^2 * c - c^2 * a = (a - b) * (b - c) * (c - a) := by 
    ring
  rw [h4]
  have h5 : abs ((a - b) * (b - c) * (c - a)) ≥ 2 := by
    have ha1 : a - b ≠ 0 := h.1 
    have hb1 : b - c ≠ 0 := h.2.1 
    have hc1 : c - a ≠ 0 := h.2.2
    have h6 : (a - b) * (b - c) * (c - a) ≠ 0 := by 
      apply mul_ne_zero 
      apply mul_ne_zero 
      exact_mod_cast ha1 
      exact_mod_cast hb1 
      exact_mod_cast hc1
    by_contra h
    push_neg at h 
    have h7 : abs ((a - b) * (b - c) * (c - a)) < 2 := by 
      linarith 
    have h8 : abs ((a - b) * (b - c) * (c - a)) = 1 := by 
      cases' abs_cases ((a - b) * (b - c) * (c - a)) with h9 h9 
      · -- Case where the product is non-negative
        omega 
      · -- Case where the product is negative 
        omega 
    have h9 : (a - b) * (b - c) * (c - a) = 1 ∨ (a - b) * (b - c) * (c - a) = -1 := by
      cases' abs_cases ((a - b) * (b - c) * (c - a)) with h9 h9 
      · -- Case where the product is non-negative 
        omega 
      · --  Case where the product is negative 
        omega 
    rcases h9 with (h9 | h9)
    · --  Case where the product is 1 
      have h9' : (a - b) * (b - c) * (c - a) = 1 := h9 
      have h10 : (a - b) ∣ 1 := by 
        use (b - c) * (c - a) 
        linarith 
      have h11 : (a - b) = 1 ∨ (a - b) = -1 := by 
        have : (a - b) ∣ 1 := h10 
        have h14 : (a - b) ≤ 1 := by 
          exact Int.le_of_dvd (by norm_num) this 
        have h15 : (a - b) ≥ -1 := by 
          have h16 : - (a - b) ∣ 1 := by 
            exact Int.neg_dvd.2 this 
          have h17 : - (a - b) ≤ 1 := by 
            exact Int.le_of_dvd (by norm_num) h16 
          omega 
        interval_cases (a - b) <;> tauto 
      rcases h11 with (h11 | h11) 
      all_goals 
        have h12 : (b - c) = 1 ∨ (b - c) = -1 := by 
          have : (b - c) ∣ 1 := by 
            use (a - b) * (c - a) 
            linarith 
          have : (b - c) ∣ 1 := by 
            use (a - b) * (c - a) 
            linarith 
          have h14 : (b - c) ≤ 1 := by 
            exact Int.le_of_dvd (by norm_num) this 
          have h15 : (b - c) ≥ -1 := by 
            have h16 : - (b - c) ∣ 1 := by
              exact Int.neg_dvd.2 this 
            have h17 : - (b - c) ≤ 1 := by 
              exact Int.le_of_dvd (by norm_num) h16 
            omega 
          interval_cases (b - c) <;> tauto 
        rcases h12 with (h12 | h12) 
        all_goals 
          have h13 : (c - a) = 1 ∨ (c - a) = -1 := by 
            have : (c - a) ∣ 1 := by 
              use (a - b) * (b - c) 
              linarith 
            have : (c - a) ∣ 1 := by 
              use (a - b) * (b - c) 
              linarith 
            have h14 : (c - a) ≤ 1 := by 
              exact Int.le_of_dvd (by norm_num) this 
            have h15 : (c - a) ≥ -1 := by 
              have h16 : - (c - a) ∣ 1 := by 
                exact Int.neg_dvd.2 this 
              have h17 : - (c - a) ≤ 1 := by 
                exact Int.le_of_dvd (by norm_num) h16 
              omega 
            interval_cases (c - a) <;> tauto 
          rcases h13 with (h13 | h13) 
          all_goals 
            omega 
    · -- Case where the product is -1 
      have h9' : (a - b) * (b - c) * (c - a) = -1 := h9 
      have h10 : (a - b) ∣ 1 := by 
        use - ((b - c) * (c - a)) 
        linarith 
      have h11 : (a - b) = 1 ∨ (a - b) = -1 := by 
        have : (a - b) ∣ 1 := h10 
        have h14 : (a - b) ≤ 1 := by 
          exact Int.le_of_dvd (by norm_num) this 
        have h15 : (a - b) ≥ -1 := by 
          have h16 : - (a - b) ∣ 1 := by 
            exact Int.neg_dvd.2 this 
          have h17 : - (a - b) ≤ 1 := by 
            exact Int.le_of_dvd (by norm_num) h16 
          omega 
        interval_cases (a - b) <;> tauto 
      rcases h11 with (h11 | h11) 
      all_goals 
        have h12 : (b - c) = 1 ∨ (b - c) = -1 := by 
          have : (b - c) ∣ 1 := by 
            use - ((a - b) * (c - a)) 
            linarith 
          have : (b - c) ∣ 1 := by 
            use - ((a - b) * (c - a)) 
            linarith 
          have h14 : (b - c) ≤ 1 := by 
            exact Int.le_of_dvd (by norm_num) this 
          have h15 : (b - c) ≥ -1 := by 
            have h16 : - (b - c) ∣ 1 := by 
              exact Int.neg_dvd.2 this 
            have h17 : - (b - c) ≤ 1 := by 
              exact Int.le_of_dvd (by norm_num) h16 
            omega 
          interval_cases (b - c) <;> tauto 
        rcases h12 with (h12 | h12) 
        all_goals 
          have h13 : (c - a) = 1 ∨ (c - a) = -1 := by 
            have : (c - a) ∣ 1 := by 
              use - ((a - b) * (b - c)) 
              linarith 
            have : (c - a) ∣ 1 := by 
              use - ((a - b) * (b - c)) 
              linarith 
            have h14 : (c - a) ≤ 1 := by 
              exact Int.le_of_dvd (by norm_num) this 
            have h15 : (c - a) ≥ -1 := by 
              have h16 : - (c - a) ∣ 1 := by 
                exact Int.neg_dvd.2 this 
              have h17 : - (c - a) ≤ 1 := by 
                exact Int.le_of_dvd (by norm_num) h16 
              omega 
            interval_cases (c - a) <;> tauto 
          rcases h13 with (h13 | h13) 
          all_goals 
            omega 
  exact_mod_cast h5