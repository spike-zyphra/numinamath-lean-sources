import Mathlib

theorem algebra_192019 (x : ℝ) (hx : 8 - x ≥ 0 ∧ 89 + x ≥ 0) :
    (8 - x) ^ ((1 : ℝ) / 4) + (89 + x) ^ ((1 : ℝ) / 4) = 5 ↔
    x = -8 ∨ x = -73 := by 
  constructor
  · -- Forward: if the equation holds, prove the roots 
    intro h_eq
    have h1 : (8 - x) ^ ((1 : ℝ) / 4) ≥ 0 := by
      apply Real.rpow_nonneg
      linarith [hx.1]
    have h2 : (89 + x) ^ ((1 : ℝ) / 4) ≥ 0 := by
      apply Real.rpow_nonneg 
      linarith [hx.2]
    have h3 : ((8 - x) ^ ((1 : ℝ) / 4)) ^ 4 = (8 - x) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith [hx.1]
    have h4 : ((89 + x) ^ ((1 : ℝ) / 4)) ^ 4 = (89 + x) := by 
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num 
      all_goals linarith [hx.2]
    have h5 : (8 - x : ℝ) ^ ((1 : ℝ) / 4) + (89 + x : ℝ) ^ ((1 : ℝ) / 4) = 5 := h_eq 
    have h7 : (8 - x : ℝ) ^ ((1 : ℝ) / 4) = 2 ∨ (8 - x : ℝ) ^ ((1 : ℝ) / 4) = 3 := by
      have h8 : ((8 - x : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 - 5 * ((8 - x : ℝ) ^ ((1 : ℝ) / 4)) + 6 = 0 := by 
        have eq1 := h_eq 
        have eq2 : ((8 - x : ℝ) ^ ((1 : ℝ) / 4) + (89 + x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = (5 ^ 4 : ℝ) := by
          rw [eq1]
        have eq3 : ((8 - x : ℝ) ^ ((1 : ℝ) / 4) + (89 + x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 =
            ((8 - x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 + 4 * ((8 - x : ℝ) ^ ((1 : ℝ) / 4)) ^ 3 * ((89 + x : ℝ) ^ ((1 : ℝ) / 4)) + 6 * ((8 - x : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 * ((89 + x : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 + 4 * ((8 - x : ℝ) ^ ((1 : ℝ) / 4)) * ((89 + x : ℝ) ^ ((1 : ℝ) / 4)) ^ 3 + ((89 + x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 := by 
          ring 
        rw [eq3] at eq2 
        rw [h3, h4] at eq2 
        nlinarith [sq_nonneg ((8 - x : ℝ) ^ ((1 : ℝ) / 4) - 2), sq_nonneg ((8 - x : ℝ) ^ ((1 : ℝ) / 4) - 3), sq_nonneg ((89 + x : ℝ) ^ ((1 : ℝ) / 4) - 2), sq_nonneg ((89 + x : ℝ) ^ ((1 : ℝ) / 4) - 3), 
          sq_nonneg ((8 - x : ℝ) ^ ((1 : ℝ) / 4) * (89 + x : ℝ) ^ ((1 : ℝ) / 4) - 6), 
          sq_nonneg ((8 - x) ^ ((1 : ℝ) / 4) ^ 2 - (89 + x) ^ ((1 : ℝ) / 4) ^ 2),
          sq_nonneg ((8 - x : ℝ) ^ ((1 : ℝ) / 4) + (89 + x : ℝ) ^ ((1 : ℝ) / 4) - 5), 
          mul_nonneg h1 h2
        ]
      have : ((8 - x : ℝ) ^ ((1 : ℝ) / 4) - 2) * ((8 - x : ℝ) ^ ((1 : ℝ) / 4) - 3) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.1 this) with h8 h9 
      · -- Case h8: (8 - x : ℝ) ^ ((1 : ℝ) / 4) - 2 = 0
        left 
        linarith 
      · -- Case h9: (8 - x : ℝ) ^ ((1 : ℝ) / 4) - 3 = 0
        right 
        linarith 
    cases h7 with 
    | inl ha2 =>
      have hx1 : x = -8 := by 
        have h8 : (8 - x : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) := by 
          linarith [ha2]
        have h9 : (8 - x) = (16 : ℝ) := by 
          calc 
            (8 - x) = ((8 - x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 := by 
              rw [← Real.rpow_natCast, ← Real.rpow_mul]
              norm_num 
              all_goals linarith [hx.1]
            _ = (2 : ℝ) ^ 4 := by 
              rw [h8]
            _ = (16 : ℝ) := by norm_num 
        linarith 
      left 
      exact hx1 
    | inr ha3 =>
      have hx2 : x = -73 := by 
        have h8 : (8 - x : ℝ) ^ ((1 : ℝ) / 4) = (3 : ℝ) := by 
          linarith [ha3]
        have h9 : (8 - x) = (81 : ℝ) := by 
          calc 
            (8 - x) = ((8 - x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 := by 
              rw [← Real.rpow_natCast, ← Real.rpow_mul]
              norm_num 
              all_goals linarith [hx.1]
            _ = (3 : ℝ) ^ 4 := by 
              rw [h8]
            _ = (81 : ℝ) := by norm_num 
        linarith 
      right 
      exact hx2 
  · -- Backward 
    rintro (h_eq | h_eq)
    · -- x = -8 
      rw [h_eq] 
      have h1 : (8 - (-8 : ℝ) ) ^ ((1 : ℝ) / 4) = (2 : ℝ) := by 
        rw [show (8 - (-8 : ℝ) ) = (16 : ℝ) by norm_num]
        have h2 : (16 : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) := by 
          rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num]
          rw [← Real.rpow_mul]
          norm_num 
          all_goals norm_num 
        exact h2 
      have h2 : (89 + (-8 : ℝ) ) ^ ((1 : ℝ) / 4) = (3 : ℝ) := by 
        rw [show (89 + (-8 : ℝ) ) = (81 : ℝ) by norm_num]
        have h3 : (81 : ℝ) ^ ((1 : ℝ) / 4) = (3 : ℝ) := by 
          rw [show (81 : ℝ) = (3 : ℝ) ^ (4 : ℝ) by norm_num]
          rw [← Real.rpow_mul]
          norm_num 
          all_goals norm_num 
        exact h3 
      rw [h1, h2] 
      all_goals norm_num 
    · -- x = -73 
      rw [h_eq] 
      have h1 : (8 - (-73 : ℝ) ) ^ ((1 : ℝ) / 4) = (3 : ℝ) := by 
        rw [show (8 - (-73 : ℝ) ) = (81 : ℝ) by norm_num]
        have h2 : (81 : ℝ) ^ ((1 : ℝ) / 4) = (3 : ℝ) := by 
          rw [show (81 : ℝ) = (3 : ℝ) ^ (4 : ℝ) by norm_num]
          rw [← Real.rpow_mul]
          norm_num 
          all_goals norm_num 
        exact h2 
      have h3 : (89 + (-73 : ℝ) ) ^ ((1 : ℝ) / 4) = (2 : ℝ) := by 
        rw [show (89 + (-73 : ℝ) ) = (16 : ℝ) by norm_num]
        have h4 : (16 : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) := by 
          rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num]
          rw [← Real.rpow_mul]
          norm_num 
          all_goals norm_num 
        exact h4 
      rw [h1, h3] 
      all_goals norm_num