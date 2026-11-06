import Mathlib

theorem inequalities_235682 (x : ℝ) : (1 : ℝ) - 27^x ≤ 6 * 9^(3 * x) ↔ x ≥ -1 / 3 := by
  constructor
  · -- Assume 1 - 27^x ≤ 6 * 9^(3*x), prove x ≥ -1/3
    intro h
    have h1 : (27 : ℝ) ^ x = 3 ^ (3 * x) := by
      rw [show (27 : ℝ) = 3 ^ (3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h2 : (9 : ℝ) ^ (3 * x) = 3 ^ (6 * x) := by
      rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    rw [h1, h2] at h
    have h3 : 1 - (3 : ℝ) ^ (3 * x) ≤ 6 * (3 : ℝ) ^ (6 * x) := by linarith
    have h4 : (3 : ℝ) ^ (6 * x) = ((3 : ℝ) ^ (3 * x)) ^ 2 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    rw [h4] at h3
    have h5 : 6 * ((3 : ℝ) ^ (3 * x)) ^ 2 + (3 : ℝ) ^ (3 * x) - 1 ≥ 0 := by linarith
    have h6 : (3 : ℝ) ^ (3 * x) ≥ (1 / 3 : ℝ) := by
      nlinarith [h5, Real.rpow_pos_of_pos (show 0 < (3 : ℝ) by norm_num) (3 * x), Real.rpow_pos_of_pos (show 0 < (3 : ℝ) by norm_num) (3 * x), Real.rpow_pos_of_pos (show 0 < (3 : ℝ) by norm_num) (3 * x)]
    have h7 : (3 : ℝ) ^ (3 * x) ≥ (1 / 3 : ℝ) := h6
    have h8 : 3 * x ≥ -1 := by
      by_contra h9
      push_neg at h9
      have h91 : (3 : ℝ) ^ (3 * x) < (1 / 3 : ℝ) := by
        have h92 : (1 / 3 : ℝ) = (3 : ℝ) ^ (-1 : ℝ) := by
          norm_num [Real.rpow_neg, Real.logb_self_eq_one]
        rw [h92]
        have h93 : (3 : ℝ) ^ (3 * x) < (3 : ℝ) ^ (-1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt 
          all_goals linarith
        linarith
      linarith [h7, h91]
    linarith 
  · -- Assume x ≥ -1/3, prove 1 - 27^x ≤ 6 * 9^(3*x)
    intro h
    have h1 : (27 : ℝ) ^ x = 3 ^ (3 * x) := by
      rw [show (27 : ℝ) = 3 ^ (3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h2 : (9 : ℝ) ^ (3 * x) = 3 ^ (6 * x) := by
      rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    rw [h1, h2]
    have h3 : 3 * x ≥ -1 := by 
      linarith 
    have h4 : (3 : ℝ) ^ (3 * x) ≥ (1 / 3 : ℝ) := by
      have h5 : (1 / 3 : ℝ) = (3 : ℝ) ^ (-1 : ℝ) := by
        norm_num [Real.rpow_neg, Real.logb_self_eq_one]
      rw [h5]
      have h6 : (3 : ℝ) ^ (3 * x) ≥ (3 : ℝ) ^ (-1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le 
        all_goals linarith 
      linarith 
    have h7 : (3 : ℝ) ^ (6 * x) = ((3 : ℝ) ^ (3 * x)) ^ 2 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    rw [h7]
    nlinarith [sq_nonneg ((3 : ℝ) ^ (3 * x) - (1 / 3 : ℝ)), Real.rpow_pos_of_pos (show 0 < (3 : ℝ) by norm_num) (3 * x), Real.rpow_pos_of_pos (show 0 < (3 : ℝ) by norm_num) (3 * x), Real.rpow_pos_of_pos (show 0 < (3 : ℝ) by norm_num) (3 * x)]