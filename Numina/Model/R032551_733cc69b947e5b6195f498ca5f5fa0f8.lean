import Mathlib

theorem algebra_161374 : (11 - 6 * √2) / (45 - 29 * √2) ^ ((1 : ℝ) / 3) = 3 - √2 := by
  have h1 : ((45 - 29 * √2) : ℝ) ^ ((1 : ℝ) / 3) = (3 - √2) := by
    have h2 : ((45 - 29 * √2) : ℝ) = (3 - √2) ^ 3 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), sq_nonneg (√2 - 1), Real.sqrt_nonneg 2, pow_two_nonneg (√2), pow_two_nonneg (3 - √2), pow_two_nonneg (45 - 29 * √2)]
    rw [h2]
    have h3 : (( (3 - √2 ) ^ 3 ) : ℝ) ^ ((1 : ℝ) / 3) = (3 - √2) := by 
      have h4 : (( (3 - √2 ) ^ 3 ) : ℝ) ^ ((1 : ℝ) / 3) = (3 - √2) := by 
        have h5 : (( (3 - √2 ) ^ 3 ) : ℝ) ^ ((1 : ℝ) / 3) = (3 - √2) := by
          rw [show ( (3 - √2 ) ^ 3 ) = (3 - √2) ^3 by ring_nf]
          have h6 : (( (3 - √2 : ℝ) ) ^ 3) ^ ((1 : ℝ) / 3) = (3 - √2 : ℝ) := by
            have h8 : ( ( (3 - √2 : ℝ) ^ 3 ) ^ ((1 : ℝ) / 3) ) = (3 - √2 : ℝ) := by 
              rw [← Real.rpow_natCast, ← Real.rpow_mul]
              norm_num
              all_goals 
                nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_nonneg 2]
            linarith [h8]
          linarith [h6]
        linarith [h5]
      linarith [h4]
    linarith [h3]
  have h12 : (11 - 6 * √2) / ( (45 - 29 * √2) ^ ((1 : ℝ) / 3) ) = (3 - √2) := by
    rw [h1]
    field_simp [(show (3 - √2) ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_nonneg 2]
    )
    ]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_nonneg 2]
  linarith [h12]