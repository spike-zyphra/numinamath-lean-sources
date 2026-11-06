import Mathlib

theorem algebra_307434 (a b m : ℝ) (ha : a^4 + m = 9 * a^2) (hb : b^4 + m = 9 * b^2)
    (hroots : a ≠ b) (hsum : a + b = 4) : m = 12.25 := by

  have h_eq : a^4 - b^4 = 9 * (a^2 - b^2) := by
      nlinarith [ha, hb]

  have h2 : (a^2 - b^2) * (a^2 + b^2) = 9 * (a^2 - b^2) := by 
      nlinarith [h_eq]

  have h3 : a^2 + b^2 = 9 := by 
      have h4 : a^2 - b^2 ≠ 0 := by 
        by_contra h
        have h5 : a^2 = b^2 := by 
            nlinarith [h]
        have h6 : a = b ∨ a = -b := by 
            have h7 : a^2 = b^2 := by 
                nlinarith [h5]
            have h8 : a = b ∨ a = -b := by 
                apply eq_or_eq_neg_of_sq_eq_sq 
                all_goals nlinarith 
            exact h8 
        cases h6 with 
        | inl h9 => 
            exfalso 
            exact hroots (by linarith) 
        | inr h10 => 
            have h7 : a + b = 0 := by 
                nlinarith [h10] 
            linarith [hsum, h7] 
      have h5 : a^2 + b^2 = 9 := by 
          apply (mul_left_inj' h4).mp 
          linarith [h2] 
      linarith [h5]

  have h6 : a * b = 3.5 := by 
      have h7 : (a + b)^2 = a^2 + 2 * (a * b) + b^2 := by ring
      have h9 : (a + b)^2 = 16 := by nlinarith [hsum]
      nlinarith [h9, h3]

  have ha_eq : a^2 = 4 * a - 3.5 := by 
      have h8 : b = 4 - a := by linarith [hsum]
      have hb_eq : b^2 = 4 * b - 3.5 := by 
          nlinarith [hb, ha, h3, h6, hsum, sq_pos_of_ne_zero (sub_ne_zero.mpr hroots)]
      rw [h8] at hb_eq 
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hroots)]

  have hm : m = 9 * a^2 - a^4 := by 
      nlinarith [ha]

  rw [hm] 
  have ha_4 : a^4 = (4 * a - 3.5) ^ 2 := by 
      calc 
        a^4 = (a^2) ^ 2 := by ring 
        _ = (4 * a - 3.5) ^ 2 := by rw [ha_eq] 

  rw [ha_4]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 4), sq_nonneg (a * b - 3.5), sq_nonneg (a^2 + b^2 - 9)]