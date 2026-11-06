import Mathlib

theorem algebra_357 :
  {(a, b) : ℤ × ℤ | a ≠ b ∧ a^2 - b^2 = (a - b)^5 ∧ a^2 < 100 ∧ b^2 < 100} = {(1, 0), (0, 1), (9, 7), (7, 9)} := by
  ext ⟨a, b⟩ 
  simp
  constructor
  · -- Assume ⟨a, b⟩ is in the left side 
    rintro ⟨h1, h2, h3, h4⟩ 
    have h5 : a^2 - b^2 = (a - b)^5 := h2 
    have h6 : (a - b) * (a + b) = (a - b)^5 := by 
      linarith 
    by_cases h7 : a - b = 0 
    · -- a - b = 0 
      have h8 : a = b := by 
        linarith 
      omega -- contradiction with a ≠ b 
    · -- a - b ≠ 0 
      have eq1 : a + b = (a - b) ^ 4 := by 
        apply (mul_right_inj' h7).mp 
        linarith 
      have h8 : a ≤ 9 := by 
        nlinarith 
      have h9 : a ≥ -9 := by 
        nlinarith 
      have h10 : b ≤ 9 := by 
        nlinarith 
      have h11 : b ≥ -9 := by 
        nlinarith 
      have eq14 : (a - b) ≤ 2 := by 
        by_contra h15 
        push_neg at h15 
        have h16 : (a - b) ≥ 3 := by 
          omega 
        have h17 : (a - b : ℤ) ^ 4 ≥ 81 := by 
          have h18 : (a - b : ℤ) ≥ 3 := by 
            omega 
          have h19 : (a - b : ℤ) ^ 4 ≥ (3 : ℤ) ^ 4 := by
            have h40 : (a - b : ℤ) ≥ (3 : ℤ) := by linarith 
            have h41 : (a - b : ℤ) ^ 4 ≥ ((3 : ℤ) ) ^ 4 := by
              apply pow_le_pow_left 
              all_goals 
                linarith
            linarith
          linarith
        have h18 : (a + b) ≥ 81 := by 
          linarith [eq1, h17] 
        nlinarith 
      have eq19 : (a - b) ≥ -2 := by 
        by_contra h20 
        push_neg at h20 
        have h21 : (a - b) ≤ -3 := by 
          omega 
        have h22 : (a - b) ^ 4 ≥ 81 := by 
          have h23 : (a - b : ℤ) ≤ -3 := by 
            omega 
          have h42 : (a - b) ≤ -3 := h23
          have h43 : (a - b : ℤ) ^ 2 ≥ 9 := by 
            nlinarith [sq_nonneg ((a - b : ℤ) + 3)]
          have h44 : (a - b : ℤ) ^ 4 ≥ 81 := by 
            nlinarith [sq_nonneg ((a - b : ℤ) ^ 2), h43, sq_nonneg ((a - b : ℤ) + 3), sq_nonneg ((a - b) - (-3))]
          linarith
        have h23 : (a + b) ≥ 81 := by 
          linarith [eq1, h22] 
        nlinarith 
      have h24 : (a - b) = -2 ∨ (a - b) = -1 ∨ (a - b) = 1 ∨ (a - b) = 2 := by 
        have hneq0 : a - b ≠ 0 := by 
          intro heq0 
          apply h7 
          omega 
        have eq14 : (a - b) ≤ 2 := eq14
        have eq19 : (a - b) ≥ -2 := eq19
        omega 
      rcases h24 with (h24 | h24 | h24 | h24) 
      · -- a - b = -2 
        have h25 : a + b = 16 := by 
          rw [show a - b = -2 by linarith [h24]] at eq1 
          nlinarith 
        have ha : a = 7 := by 
          linarith [h25, h24] 
        have hb : b = 9 := by 
          linarith [h25, h24] 
        norm_num [ha, hb] 
      · -- a - b = -1 
        have h26 : a + b = 1 := by 
          rw [show a - b = -1 by linarith [h24]] at eq1 
          nlinarith 
        have ha : a = 0 := by 
          linarith [h26, h24] 
        have hb : b = 1 := by 
          linarith [h26, h24] 
        norm_num [ha, hb] 
      · -- a - b = 1 
        have h27 : a + b = 1 := by 
          rw [show a - b = 1 by linarith [h24]] at eq1 
          nlinarith 
        have ha : a = 1 := by 
          linarith [h27, h24] 
        have hb : b = 0 := by 
          linarith [h27, h24] 
        norm_num [ha, hb] 
      · -- a - b = 2 
        have h28 : (a + b) = 16 := by 
          rw [show (a - b) = 2 by linarith [h24]] at eq1 
          nlinarith 
        have ha : a = 9 := by 
          linarith [h28, h24] 
        have hb : b = 7 := by 
          linarith [h28, h24] 
        norm_num [ha, hb] 
  · -- Show that (1, 0), (0, 1), (9, 7), (7, 9) satisfy the condition 
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) 
    · -- Check (1, 0) 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num 
    · -- Check (0, 1) 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num 
    · -- Check (9, 7) 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num 
    · -- Check (7, 9) 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num