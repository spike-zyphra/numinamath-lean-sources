import Mathlib
theorem algebra_187250 (x : ℝ) (hx : x ≠ -4) (h : 0 < (3 * x - 1) / (x + 4)) :
    Real.sqrt ((3 * x - 1) / (x + 4)) + 3 - 4 * Real.sqrt ((x + 4) / (3 * x - 1)) = 0 ↔
    x = 5 / 2 := by
  constructor
  · -- Assume the equation holds, prove x = 5/2
    intro h_eq 
    have h1 : (3 * x - 1) / (x + 4) > 0 := h 
    have h2 : (x + 4) / (3 * x - 1) > 0 := by 
      by_contra h3 
      push_neg at h3 
      by_cases h3x1 : 3 * x - 1 > 0 
      · -- If 3 * x - 1 > 0, then x + 4 ≤ 0.
        have h4 : x + 4 ≤ 0 := by 
          by_contra h4 
          push_neg at h4 
          have : (x + 4) / (3 * x - 1) > 0 := by 
            apply div_pos 
            all_goals linarith 
          nlinarith 
        have h5 : x ≤ -4 := by linarith 
        have h5' : x = -4 := by linarith 
        contradiction 
      by_cases h6 : 3 * x - 1 < 0 
      · -- If 3 * x - 1 < 0, then x + 4 ≥ 0.
        have h7 : x + 4 ≥ 0 := by 
          by_contra h4 
          push_neg at h4 
          have : (x + 4) / (3 * x - 1) > 0 := by 
            apply div_pos_of_neg_of_neg 
            all_goals linarith 
          nlinarith 
        have h8 : x + 4 < 0 := by 
          by_contra h9 
          push_neg at h9 
          have h9' : (3 * x - 1) / (x + 4) ≤ (0 : ℝ) := by 
            apply div_nonpos_of_nonpos_of_nonneg 
            · -- Show 3 * x - 1 ≤ 0 
              nlinarith 
            · -- Show x + 4 ≥ 0 
              nlinarith 
          linarith 
        nlinarith 
      · -- 3 * x - 1 = 0
        have h8 : 3 * x - 1 = 0 := by linarith 
        rw [h8] at h 
        norm_num at h 
    have h5 : (3 * x - 1) / (x + 4) = 1 := by 
      have h6 : (3 * x - 1) / (x + 4) > 0 := h1 
      have h7 : (x + 4) / (3 * x - 1) > 0 := h2 
      have h_eq1 : Real.sqrt ((3 * x - 1) / (x + 4)) + 3 - 4 * Real.sqrt ((x + 4) / (3 * x - 1)) = 0 := h_eq 
      have pos1 : Real.sqrt ((3 * x - 1) / (x + 4)) ≥ 0 := by positivity 
      have pos2 : Real.sqrt ((x + 4) / (3 * x - 1)) ≥ 0 := by positivity 
      have h9 : Real.sqrt ((3 * x - 1) / (x + 4)) * Real.sqrt ((x + 4) / (3 * x - 1)) = 1 := by 
        have h10 : Real.sqrt ((3 * x - 1) / (x + 4)) * Real.sqrt ((x + 4) / (3 * x - 1)) = Real.sqrt (((3 * x - 1) / (x + 4)) * ((x + 4) / (3 * x - 1)) ) := by 
          rw [← Real.sqrt_mul (by positivity)]
        rw [h10]
        have h11 : ((3 * x - 1) / (x + 4)) * ((x + 4) / (3 * x - 1)) = 1 := by 
          field_simp [(show x + 4 ≠ 0 by 
            by_contra h8 
            apply hx 
            linarith 
          ), (show 3 * x - 1 ≠ 0 by 
            by_contra h8 
            have h8' : (3 * x - 1) = (0 : ℝ) := by linarith 
            rw [h8'] at h6 
            norm_num at h6 
            all_goals linarith 
          )] 
        rw [h11] 
        all_goals norm_num 
      nlinarith [Real.sqrt_nonneg ((3 * x - 1) / (x + 4)), Real.sqrt_nonneg ((x + 4) / (3 * x - 1)), 
        sq_nonneg (Real.sqrt ((3 * x - 1) / (x + 4)) - 1), sq_nonneg (Real.sqrt ((x + 4) / (3 * x - 1)) - 1), 
        Real.sq_sqrt (show (3 * x - 1) / (x + 4) ≥ 0 by positivity), 
        Real.sq_sqrt (show (x + 4) / (3 * x - 1) ≥ 0 by positivity), h9
        ] 
    have h6 : x = 5 / 2 := by 
      have h7 : (3 * x - 1) / (x + 4) = 1 := h5 
      have h8 : x + 4 ≠ 0 := by 
        intro h8 
        apply hx 
        linarith 
      field_simp [h8] at h7 
      nlinarith 
    linarith
  · -- Assume x = 5/2, prove the equation 
    intro h_eq 
    have h1 : (3 * x - 1) / (x + 4) = 1 := by 
      have h0 : x = 5 / 2 := h_eq 
      rw [h0]
      norm_num 
    have h4 : Real.sqrt ((3 * x - 1) / (x + 4)) = (1 : ℝ) := by 
      rw [h1]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    have h5 : (x + 4) / (3 * x - 1) = (1 : ℝ) := by 
      have h0 : x = 5 / 2 := h_eq 
      rw [h0]
      norm_num 
    have h6 : Real.sqrt ((x + 4) / (3 * x - 1)) = (1 : ℝ) := by 
      rw [h5]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    rw [h4, h6]
    all_goals norm_num