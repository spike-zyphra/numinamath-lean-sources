import Mathlib

theorem algebra_178 : 1 / (1 - (3 : ℝ) ^ ((1 : ℝ) / 4)) + 1 / (1 + (3 : ℝ) ^ ((1 : ℝ) / 4)) + 2 / (1 + (3 : ℝ) ^ ((1 : ℝ) / 2)) = -2 := by
  have h1 : (3 : ℝ) ^ ((1 : ℝ) / 2) = ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by
    have h2 : ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = (3 : ℝ) ^ (2 * (1 / 4 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      ring
      all_goals norm_num
    have h3 : 2 * (1 / 4 : ℝ) = (1 / 2 : ℝ) := by norm_num
    rw [h3] at h2
    linarith
  have h3 : (1 - (3 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 := by
    have h4 : (3 : ℝ) ^ ((1 : ℝ) / 4) > 1 := by
      have h10 : (3 : ℝ) ^ ((1 : ℝ) / 4) > (1 : ℝ) := by
        have h6 : (1 : ℝ) < (3 : ℝ) := by norm_num
        have h7 : (3 : ℝ) ^ ((1 : ℝ) / 4) > (1 : ℝ) ^ ((1 : ℝ) / 4) := by
          apply Real.rpow_lt_rpow
          · linarith
          · linarith
          all_goals norm_num
        have h8 : (1 : ℝ) ^ ((1 : ℝ) / 4) = 1 := by
          simp
        nlinarith
      linarith
    have h10 : (3 : ℝ) ^ ((1 : ℝ) / 4) > 1 := h4
    have h13 : (1 - (3 : ℝ) ^ ((1 : ℝ) / 4)) < 0 := by linarith
    have h14 : (1 - (3 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 := by
      nlinarith
    exact h14
  have h40 : (1 + (3 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 := by
    have h4 : (3 : ℝ) ^ ((1 : ℝ) / 4) > 0 := by positivity
    nlinarith
  have h50 : (1 + (3 : ℝ) ^ ((1 : ℝ) / 2)) ≠ 0 := by
    have h6 : (3 : ℝ) ^ ((1 : ℝ) / 2) > 0 := by positivity
    nlinarith
  have h60 : 1 / (1 - (3 : ℝ) ^ ((1 : ℝ) / 4)) + 1 / (1 + (3 : ℝ) ^ ((1 : ℝ) / 4)) = 2 / (1 - (3 : ℝ) ^ ((1 : ℝ) / 2)) := by
    have h7 : (3 : ℝ) ^ ((1 : ℝ) / 2) = ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := h1
    rw [h7] 
    field_simp [(show (1 - (3 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 by assumption), (show (1 + (3 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 by assumption), 
      show (1 - ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2) ≠ 0 by
        have h12 : (1 - ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2) < (0 : ℝ) := by
          have h10 : (3 : ℝ) ^ ((1 : ℝ) / 4) > (1 : ℝ) := by
            have h10 : (3 : ℝ) ^ ((1 : ℝ) / 4) > (1 : ℝ) := by
              have h6 : (1 : ℝ) < (3 : ℝ) := by norm_num
              have h7 : (3 : ℝ) ^ ((1 : ℝ) / 4) > (1 : ℝ) ^ ((1 : ℝ) / 4) := by
                apply Real.rpow_lt_rpow
                · linarith
                · linarith
                all_goals norm_num
              have h8 : (1 : ℝ) ^ ((1 : ℝ) / 4) = 1 := by
                simp
              nlinarith
            linarith
          have h30 : ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 > (1 : ℝ) := by
            nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < (3 : ℝ) by norm_num) (1 / 4: ℝ)]
          nlinarith
        have h11 : (1 - ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2) ≠ 0 := by
          nlinarith
        exact h11
    ]
    nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < (3 : ℝ) by norm_num) (1 / 4: ℝ)]
  rw [h60]
  have ha4 : (3 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 3 := by
    rw [Real.sqrt_eq_rpow]
  rw [ha4]
  have ha3 : (0 : ℝ) < Real.sqrt 3 := by 
    positivity
  field_simp [(show (1 - Real.sqrt 3 : ℝ) ≠ 0 by 
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)) ]
  ), 
    show (1 + Real.sqrt 3 : ℝ) ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ) ) ]
  ]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ) ) ]