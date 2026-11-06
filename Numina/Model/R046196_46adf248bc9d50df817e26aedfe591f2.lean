import Mathlib

theorem algebra_266267 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ^ b = b ^ a) (h1 : a < 1) :
    a = b := by
  by_cases h2 : b < 1
  · -- Assume b < 1. We need to show a = b.
    have h3 : a ^ b = b ^ a := hab
    -- Take the logarithms
    have h4 : b * (Real.log a) = a * (Real.log b) := by
      have h5 : a ^ b = b ^ a := h3
      have h6 : Real.log (a ^ b) = Real.log (b ^ a) := by
        rw [h5]
      have h7 : Real.log (a ^ b) = b * Real.log a := by
        rw [Real.log_rpow]
        all_goals linarith
      have h8 : Real.log (b ^ a) = a * Real.log b := by
        rw [Real.log_rpow]
        all_goals linarith
      rw [h7, h8] at h6
      nlinarith
    have h5 : Real.log a / a = Real.log b / b := by
      have h6 : b * Real.log a = a * Real.log b := h4
      have h7 : a ≠ 0 := by linarith
      have h8 : b ≠ 0 := by linarith
      field_simp [h7, h8] at *
      nlinarith
    have h6 : a = b := by
      by_cases h7 : a < b
      · -- Assume a < b. We'll show a contradiction.
        have h8 : Real.log a < Real.log b := by
          apply Real.log_lt_log
          all_goals linarith
        have h24 : Real.log a / a < Real.log b / b := by
          have h11 : Real.log a < Real.log b := h8
          have h13 : a > 0 := by linarith
          have h14 : b > 0 := by linarith
          have h15 : Real.log a < 0 := by
            have h16 : a < 1 := by linarith
            have h17 : Real.log a < Real.log (1 : ℝ) := by
              apply Real.log_lt_log
              all_goals linarith
            have h18 : Real.log (1 : ℝ) = 0 := Real.log_one
            linarith [h17, h18]
          have h16 : Real.log b < 0 := by
            have h17 : b < 1 := by linarith
            have h18 : Real.log b < Real.log (1 : ℝ) := by
              apply Real.log_lt_log
              all_goals linarith
            have h19 : Real.log (1 : ℝ) = 0 := Real.log_one
            linarith [h18, h19]
          have h23 : a < b := h7
          apply (div_lt_div_iff (by linarith) (by linarith)).mpr
          nlinarith [sq_pos_of_pos h13, sq_pos_of_pos h14, h11, sq_nonneg (Real.log a - Real.log b), sq_nonneg (a - b), mul_pos ha hb]
        linarith [h5, h24]
      by_cases h7 : a > b
      · -- Assume a > b. We'll show a contradiction.
        have h8 : Real.log a > Real.log b := by
          apply Real.log_lt_log
          all_goals linarith
        have h24 : Real.log a / a > Real.log b / b := by
          have h11 : Real.log a > Real.log b := h8
          have h13 : a > 0 := by linarith
          have h14 : b > 0 := by linarith
          have h15 : Real.log a < 0 := by
            have h16 : a < 1 := by linarith
            have h17 : Real.log a < Real.log (1 : ℝ) := by
              apply Real.log_lt_log
              all_goals linarith
            have h18 : Real.log (1 : ℝ) = 0 := Real.log_one
            linarith [h17, h18]
          have h16 : Real.log b < 0 := by
            have h17 : b < 1 := by linarith
            have h18 : Real.log b < Real.log (1 : ℝ) := by
              apply Real.log_lt_log
              all_goals linarith
            have h19 : Real.log (1 : ℝ) = 0 := Real.log_one
            linarith [h18, h19]
          have h23 : a > b := h7
          apply (div_lt_div_iff (by linarith) (by linarith)).mpr
          nlinarith [sq_pos_of_pos h13, sq_pos_of_pos h14, h11, sq_nonneg (Real.log a - Real.log b), sq_nonneg (a - b), mul_pos ha hb]
        linarith [h5, h24]
      · -- a = b
        linarith
    linarith
  · -- Case b ≥ 1
    push_neg at h2
    have h16 : b < 1 := by
      by_contra h16
      push_neg at h16
      have h17 : b ≥ 1 := by linarith
      have h18 : a ^ b < 1 := by
        apply Real.rpow_lt_one
        all_goals nlinarith
      have h19 : b ^ a ≥ 1 := by
        apply Real.one_le_rpow
        linarith
        all_goals nlinarith
      have h20 : a ^ b < b ^ a := by
        nlinarith
      nlinarith [h20, hab]
    have h3 : a ^ b = b ^ a := hab
    have h4 : b * (Real.log a) = a * (Real.log b) := by
      have h5 : a ^ b = b ^ a := h3
      have h6 : Real.log (a ^ b) = Real.log (b ^ a) := by
        rw [h5]
      have h7 : Real.log (a ^ b) = b * Real.log a := by
        rw [Real.log_rpow]
        all_goals linarith
      have h8 : Real.log (b ^ a) = a * Real.log b := by
        rw [Real.log_rpow]
        all_goals linarith
      rw [h7, h8] at h6
      nlinarith
    have h5 : Real.log a / a = Real.log b / b := by
      have h6 : b * Real.log a = a * Real.log b := h4
      have h7 : a ≠ 0 := by linarith
      have h8 : b ≠ 0 := by linarith
      field_simp [h7, h8] at *
      nlinarith
    have h6 : a = b := by
      by_cases h7 : a < b
      · -- Assume a < b. We'll show a contradiction.
        have h8 : Real.log a < Real.log b := by
          apply Real.log_lt_log
          all_goals linarith
        have h9 : Real.log a / a < Real.log b / b := by
          have h11 : Real.log a < Real.log b := h8
          have h13 : a > 0 := by linarith
          have h14 : b > 0 := by linarith
          have h15 : Real.log a < 0 := by
            have h16 : a < 1 := by linarith
            have h17 : Real.log a < Real.log (1 : ℝ) := by
              apply Real.log_lt_log
              all_goals linarith
            have h18 : Real.log (1 : ℝ) = 0 := Real.log_one
            linarith [h17, h18]
          have h16 : Real.log b < 0 := by
            have h17 : b < 1 := by nlinarith
            have h18 : Real.log b < Real.log (1 : ℝ) := by
              apply Real.log_lt_log
              all_goals linarith
            have h19 : Real.log (1 : ℝ) = 0 := Real.log_one
            linarith [h18, h19]
          have h23 : a < b := h7
          apply (div_lt_div_iff (by linarith) (by linarith)).mpr
          nlinarith [sq_pos_of_pos h13, sq_pos_of_pos h14, h11, sq_nonneg (Real.log a - Real.log b), sq_nonneg (a - b), mul_pos ha hb]
        linarith [h5, h9]
      by_cases h7 : a > b
      · -- Assume a > b. We'll show a contradiction.
        have h8 : Real.log a > Real.log b := by
          apply Real.log_lt_log
          all_goals linarith
        have h9 : Real.log a / a > Real.log b / b := by
          have h11 : Real.log a > Real.log b := h8
          have h13 : a > 0 := by linarith
          have h14 : b > 0 := by linarith
          have h15 : Real.log a < 0 := by
            have h16 : a < 1 := by linarith
            have h17 : Real.log a < Real.log (1 : ℝ) := by
              apply Real.log_lt_log
              all_goals linarith
            have h18 : Real.log (1 : ℝ) = 0 := Real.log_one
            linarith [h17, h18]
          have h16 : Real.log b < 0 := by
            have h17 : b < 1 := by nlinarith
            have h18 : Real.log b < Real.log (1 : ℝ) := by
              apply Real.log_lt_log
              all_goals linarith
            have h19 : Real.log (1 : ℝ) = 0 := Real.log_one
            linarith [h18, h19]
          have h23 : a > b := h7
          apply (div_lt_div_iff (by linarith) (by linarith)).mpr
          nlinarith [sq_pos_of_pos h13, sq_pos_of_pos h14, h11, sq_nonneg (Real.log a - Real.log b), sq_nonneg (a - b), mul_pos ha hb]
        linarith [h5, h9]
      · -- a = b
        linarith
    linarith