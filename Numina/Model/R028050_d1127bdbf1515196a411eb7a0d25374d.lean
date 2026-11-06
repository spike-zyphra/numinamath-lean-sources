import Mathlib

theorem algebra_205 : (3 : ℝ) ^ ((1 : ℝ) / 3) * ((4 / 9) ^ ((1 : ℝ) / 3) - (2 / 9) ^ ((1 : ℝ) / 3) + (1 / 9) ^ ((1 : ℝ) / 3)) ^ (-1 : ℝ) = (2 ^ ((1 : ℝ) / 3) + 1) := by

  have h1 : (4 / 9 : ℝ) ^ ((1 : ℝ) / 3) = (4 : ℝ) ^ ((1 : ℝ) / 3) / (9 : ℝ) ^ ((1 : ℝ) / 3) := by 
    rw [← Real.div_rpow]
    all_goals norm_num

  have h2 : (2 / 9 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ ((1 : ℝ) / 3) / (9 : ℝ) ^ ((1 : ℝ) / 3) := by 
    rw [← Real.div_rpow]
    all_goals norm_num

  have h3 : (1 / 9 : ℝ) ^ ((1 : ℝ) / 3) = 1 / (9 : ℝ) ^ ((1 : ℝ) / 3) := by
    have h4 : (1 / 9 : ℝ) ^ ((1 : ℝ) / 3) = (1 : ℝ) ^ ((1 : ℝ) / 3) / (9 : ℝ) ^ ((1 : ℝ) / 3) := by 
      rw [← Real.div_rpow]
      all_goals norm_num
    rw [h4]
    have h5 : (1 : ℝ) ^ ((1 : ℝ) / 3) = 1 := by 
      simp 
    rw [h5]

  rw [h1, h2, h3]

  have h5 : ( ( (4 : ℝ) ^ ((1 : ℝ) / 3) / (9 : ℝ) ^ ((1 : ℝ) / 3) ) - ( (2 : ℝ) ^ ((1 : ℝ) / 3) / (9 : ℝ) ^ ((1 : ℝ) / 3) ) + (1 / (9 : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ (-1 : ℝ) = (9 : ℝ) ^ ((1 : ℝ) / 3) / ( (4 : ℝ) ^ ((1 : ℝ) / 3) - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 ) := by 
    have h6 : ( ( (4 : ℝ) ^ ((1 : ℝ) / 3) / (9 : ℝ) ^ ((1 : ℝ) / 3) ) - ( (2 : ℝ) ^ ((1 : ℝ) / 3) / (9 : ℝ) ^ ((1 : ℝ) / 3) ) + (1 / (9 : ℝ) ^ ((1 : ℝ) / 3) ) ) = ( (4 : ℝ) ^ ((1 : ℝ) / 3) - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 ) / (9 : ℝ) ^ ((1 : ℝ) / 3) := by 
      field_simp 
      <;> ring 
    rw [h6]
    have h6 : ( ( (4 : ℝ) ^ ((1 : ℝ) / 3) - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 ) / (9 : ℝ) ^ ((1 : ℝ) / 3) ) ^ (-1 : ℝ) = (9 : ℝ) ^ ((1 : ℝ) / 3) / ( (4 : ℝ) ^ ((1 : ℝ) / 3) - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 ) := by
      have h6 : ( ( (4 : ℝ) ^ ((1 : ℝ) / 3) - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 ) / (9 : ℝ) ^ ((1 : ℝ) / 3) ) ≠ 0 := by
        apply div_ne_zero
        · -- Show that numerator is not zero
          have h8 : (4 : ℝ) ^ ((1 : ℝ) / 3) - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 ≠ 0 := by
            have h10 : (4 : ℝ) ^ ((1 : ℝ) / 3) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by 
              have h4_a : (4 : ℝ) ^ ((1 : ℝ) / 3) = ((2 : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 3) := by
                norm_num 
              have h4_b : ((2 : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ (2 * (1 / 3 : ℝ)) := by
                rw [← Real.rpow_mul]
                ring_nf
                all_goals norm_num
              have h4_c : (2 : ℝ) ^ (2 * (1 / 3 : ℝ)) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by 
                have h7 : (2 : ℝ) ^ (2 * (1 / 3 : ℝ)) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by 
                  rw [← Real.rpow_natCast, ← Real.rpow_mul]
                  ring_nf
                  all_goals norm_num 
                linarith [h7]
              rw [h4_a, h4_b, h4_c]
            rw [h10]
            have h9 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 > 0 := by 
              have ha : (2 : ℝ) ^ ((1 : ℝ) / 3) > 0 := by positivity
              nlinarith [sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1 / 2)]
            linarith 
          exact h8 
        · -- Show the denominator is not zero
          positivity 
      rw [Real.rpow_neg_one]
      field_simp [h6]
    exact h6

  rw [h5]

  have h14 : (4 : ℝ) ^ ((1 : ℝ) / 3) - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 := by 
    have h4_a : (4 : ℝ) ^ ((1 : ℝ) / 3) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by 
      have h4_a : (4 : ℝ) ^ ((1 : ℝ) / 3) = ((2 : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 3) := by
        norm_num 
      have h4_b : ((2 : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ (2 * (1 / 3 : ℝ)) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals norm_num 
      have h4_c : (2 : ℝ) ^ (2 * (1 / 3 : ℝ)) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by 
        have h7 : (2 : ℝ) ^ (2 * (1 / 3 : ℝ)) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by 
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf
          all_goals norm_num 
        linarith [h7]
      rw [h4_a, h4_b, h4_c]
    linarith [h4_a]

  rw [h14]

  have h15 : (9 : ℝ) ^ ((1 : ℝ) / 3) = ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by 
    have h16 : (9 : ℝ) ^ ((1 : ℝ) / 3) = (3 : ℝ) ^ (2 * (1 / 3) : ℝ) := by
      rw [show (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num 
    have h17 : (3 : ℝ) ^ (2 * (1 / 3) : ℝ) = ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by 
      have h18 : (3 : ℝ) ^ (2 * (1 / 3) : ℝ) = ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by 
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring_nf
        all_goals norm_num 
      linarith [h18]
    rw [h16, h17]

  rw [h15]

  have h16 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 3 := by 
    have h17 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (3 : ℝ) := by 
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith 
    linarith

  have h18 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (2 : ℝ) := by 
    have h19 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (2 : ℝ) := by 
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith 
    linarith

  field_simp [show ( ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 ) ≠ 0 by
    have h9 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 > 0 := by
      have ha : (2 : ℝ) ^ ((1 : ℝ) / 3) > 0 := by positivity
      nlinarith [sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1 / 2) ]
    positivity
  ]
  nlinarith [ sq_nonneg (((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 - 1), sq_nonneg (((2 : ℝ) ^ ((1 : ℝ) / 3)) - 1), sq_nonneg (((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 - 3), h16, h18 ]