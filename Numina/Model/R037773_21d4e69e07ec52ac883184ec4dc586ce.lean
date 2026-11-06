import Mathlib
theorem algebra_123343 (a b c : ℤ) :
    a^2 = b * c + 1 ∧ b^2 = c * a + 1 ↔
    (a = 1 ∧ b = 1 ∧ c = 0) ∨
    (a = -1 ∧ b = -1 ∧ c = 0) ∨
    (a = 1 ∧ b = -1 ∧ c = 0) ∨
    (a = -1 ∧ b = 1 ∧ c = 0) ∨
    (a = 1 ∧ b = 0 ∧ c = -1) ∨
    (a = -1 ∧ b = 0 ∧ c = 1) ∨
    (a = 0 ∧ b = 1 ∧ c = -1) ∨
    (a = 0 ∧ b = -1 ∧ c = 1) := by
  constructor
  · -- Assume the equations hold, prove one of the solutions
    rintro ⟨h1, h2⟩
    have h3 : (a - b) * (a + b) = c * (b - a) := by 
      nlinarith
    have h4 : (a - b) * (a + b + c) = 0 := by
      linarith 
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- case $a - b = 0$
      have hab : a = b := by 
        linarith 
      rw [show b = a by linarith [hab] ] at h1 
      have h6 : a * (a - c) = 1 := by 
        nlinarith 
      have h7 : a = 1 ∨ a = -1 := by 
        have h8 : a * (a - c) = 1 := h6
        have h9 : a ∣ 1 := by 
          use (a - c) 
          all_goals linarith 
        have h10 : a = 1 ∨ a = -1 := by 
          have h11 : a ∣ 1 := h9 
          have h12 : a ≤ 1 := by 
            apply Int.le_of_dvd (by norm_num) h11 
          have h13 : a ≥ -1 := by 
            have h14 : (-a) ∣ 1 := by 
              exact Int.neg_dvd.2 h11 
            have h15 : -a ≤ 1 := by 
              apply Int.le_of_dvd (by norm_num) h14 
            omega 
          interval_cases a <;> try { tauto }
        exact h10 
      cases' h7 with h7 h7 
      · -- case $a = 1$
        have ha : a = 1 := h7 
        have hb : b = 1 := by linarith [hab, ha] 
        have hc : c = 0 := by 
          rw [show a = 1 by linarith [ha] ] at h6 
          nlinarith
        left 
        exact ⟨ha, hb, hc⟩ 
      · -- case $a = -1$
        have ha : a = -1 := h7 
        have hb : b = -1 := by linarith [hab, ha]
        have hc : c = 0 := by 
          rw [show a = -1 by linarith [ha] ] at h6 
          nlinarith
        right 
        left 
        exact ⟨ha, hb, hc⟩ 
    · -- case $a + b + c = 0$
      have h11 : c = - (a + b) := by 
        linarith 
      rw [h11] at h1
      have h12 : a^2 + a * b + b^2 = 1 := by
        nlinarith 
      have h13 : b ≤ 1 := by 
        nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
      have h14 : b ≥ -1 := by 
        nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
      interval_cases b <;> try { 
        have : a ≤ 1 := by nlinarith 
        have : a ≥ -1 := by nlinarith 
        interval_cases a <;> norm_num at h12 
          <;> norm_num [h11] at *
          <;> omega
      }
  · -- Now prove the reverse: each solution satisfies the equations.
    rintro (h | h | h | h | h | h | h | h)
    · -- (1, 1, 0)
      rcases h with ⟨ha, hb, hc⟩ 
      constructor 
      · -- Check a^2 = b * c + 1 
        rw [ha, hb, hc] 
        norm_num 
      · -- Check b^2 = c * a + 1 
        rw [hb, hc, ha] 
        norm_num 
    · -- (-1, -1, 0)
      rcases h with ⟨ha, hb, hc⟩ 
      constructor 
      · -- Check a^2 = b * c + 1 
        rw [ha, hb, hc] 
        norm_num 
      · -- Check b^2 = c * a + 1 
        rw [hb, hc, ha] 
        norm_num 
    · -- (1, -1, 0)
      rcases h with ⟨ha, hb, hc⟩ 
      constructor 
      · -- Check a^2 = b * c + 1 
        rw [ha, hb, hc] 
        norm_num 
      · -- Check b^2 = c * a + 1 
        rw [hb, hc, ha] 
        norm_num 
    · -- (-1, 1, 0)
      rcases h with ⟨ha, hb, hc⟩ 
      constructor 
      · -- Check a^2 = b * c + 1 
        rw [ha, hb, hc] 
        norm_num 
      · -- Check b^2 = c * a + 1 
        rw [hb, hc, ha] 
        norm_num 
    · -- (1, 0, -1)
      rcases h with ⟨ha, hb, hc⟩ 
      constructor 
      · -- Check a^2 = b * c + 1 
        rw [ha, hb, hc] 
        norm_num 
      · -- Check b^2 = c * a + 1 
        rw [hb, hc, ha] 
        norm_num 
    · -- (-1, 0, 1)
      rcases h with ⟨ha, hb, hc⟩ 
      constructor 
      · -- Check a^2 = b * c + 1 
        rw [ha, hb, hc] 
        norm_num 
      · -- Check b^2 = c * a + 1 
        rw [hb, hc, ha] 
        norm_num 
    · -- (0, 1, -1)
      rcases h with ⟨ha, hb, hc⟩ 
      constructor 
      · -- Check a^2 = b * c + 1 
        rw [ha, hb, hc] 
        norm_num 
      · -- Check b^2 = c * a + 1 
        rw [hb, hc, ha] 
        norm_num 
    · -- (0, -1, 1)
      rcases h with ⟨ha, hb, hc⟩ 
      constructor 
      · -- Check a^2 = b * c + 1 
        rw [ha, hb, hc] 
        norm_num 
      · -- Check b^2 = c * a + 1 
        rw [hb, hc, ha] 
        norm_num