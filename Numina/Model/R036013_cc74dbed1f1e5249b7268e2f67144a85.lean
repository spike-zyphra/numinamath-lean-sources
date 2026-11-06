import Mathlib

theorem algebra_161228 (x : ℝ) (hx : 0 ≤ x) :
    (x ^ ((1 : ℝ) / 3) + x ^ ((1 : ℝ) / 4)) = 6 * x ^ ((1 : ℝ) / 6) ↔ x = 0 ∨ x = 4096 := by
  constructor
  · -- Forward direction: if the equation holds, then x = 0 or x = 4096
    intro h_eq
    have h1 : x ^ ((1 : ℝ) / 3) = (x ^ ((1 : ℝ) / 12)) ^ 4 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h2 : x ^ ((1 : ℝ) / 4) = (x ^ ((1 : ℝ) / 12)) ^ 3 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h3 : x ^ ((1 : ℝ) / 6) = (x ^ ((1 : ℝ) / 12)) ^ 2 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      norm_num
      all_goals linarith
    rw [h1, h2, h3] at h_eq
    have h5 : (x ^ ((1 : ℝ) / 12)) ^ 2 * ((x ^ ((1 : ℝ) / 12)) ^ 2 + (x ^ ((1 : ℝ) / 12)) - 6) = 0 := by 
      nlinarith [sq_nonneg (x ^ ((1 : ℝ) / 12) ^ 2 - 4), sq_nonneg ((x ^ ((1 : ℝ) / 12)) - 2), sq_nonneg ((x ^ ((1 : ℝ) / 12)) + 3)]
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case h6: ((x ^ ((1 : ℝ) / 12)) ^ 2) = 0 
      have h8 : x ^ ((1 : ℝ) / 12) = 0 := by 
        nlinarith
      have h9 : x = 0 := by 
        by_cases h11 : x = 0 
        · exact h11 
        · -- x ≠ 0 
          have h12 : x > 0 := by 
            by_contra h 
            push_neg at h 
            have h13 : x = 0 := by linarith 
            tauto 
          -- We have x > 0
          -- We need x = 0 from h8, which is a contradiction
          have h13 : x ^ ((1 : ℝ) / 12) > 0 := by 
            apply Real.rpow_pos_of_pos 
            linarith 
          linarith 
      left 
      exact h9
    · -- Case h7: (x ^ ((1 : ℝ) / 12)) ^ 2 + (x ^ ((1 : ℝ) / 12)) - 6 = 0 
      have h8 : (x ^ ((1 : ℝ) / 12) + 3) * (x ^ ((1 : ℝ) / 12) - 2) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h8) with h9 h10 
      · -- Case h9: (x ^ ((1 : ℝ) / 12) + 3) = 0 
        have h12 : x ^ ((1 : ℝ) / 12) = -3 := by 
          linarith 
        -- This is a contradiction since x >= 0 and powers of non-negative are non-negative with certain properties
        have h13 : x ^ ((1 : ℝ) / 12) ≥ 0 := by 
          apply Real.rpow_nonneg 
          linarith 
        nlinarith 
      · -- Case h10: (x ^ ((1 : ℝ) / 12) - 2) = 0 
        have h14 : x ^ ((1 : ℝ) / 12) = 2 := by 
          linarith 
        have h15 : x = (x ^ ((1 : ℝ) / 12)) ^ (12 : ℕ) := by 
          rw [← Real.rpow_natCast] 
          rw [← Real.rpow_mul] 
          norm_num 
          all_goals linarith 
        rw [h14] at h15 
        have h16 : x = (4096 : ℝ) := by 
          norm_num at h15 ⊢ 
          linarith 
        right 
        linarith 
  · -- Backward direction: if x = 0 or x = 4096, then the equation holds 
    rintro (h | h)
    · -- x = 0 
      rw [h]
      norm_num 
    · -- x = 4096 
      rw [h]
      have h1 : (4096 : ℝ) ^ ((1 : ℝ) / 3) = 16 := by 
        rw [show (4096 : ℝ) = (2 : ℝ) ^ (12 : ℕ) by norm_num]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul] 
        norm_num 
        all_goals norm_num 
      have h2 : (4096 : ℝ) ^ ((1 : ℝ) / 4) = 8 := by 
        rw [show (4096 : ℝ) = (2 : ℝ) ^ (12 : ℕ) by norm_num]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul] 
        norm_num 
        all_goals norm_num 
      have h3 : (4096 : ℝ) ^ ((1 : ℝ) / 6) = 4 := by 
        rw [show (4096 : ℝ) = (2 : ℝ) ^ (12 : ℕ) by norm_num]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul] 
        norm_num 
        all_goals norm_num 
      rw [h1, h2, h3] 
      all_goals norm_num