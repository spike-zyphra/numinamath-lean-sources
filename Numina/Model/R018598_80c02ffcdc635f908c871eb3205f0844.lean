import Mathlib

theorem algebra_177480 : (Real.sqrt 2 - 1) / (Real.sqrt 2 + 1) = (10 - 7 * Real.sqrt 2) ^ ((1 : ℝ) / 3) / (10 + 7 * Real.sqrt 2) ^ ((1 : ℝ) / 3) := by
  have h1 : Real.sqrt 2 > 0 := by 
    apply Real.sqrt_pos.mpr 
    linarith
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)
  have h3 : (Real.sqrt 2 + 1) ≠ 0 := by 
    nlinarith [h1]

  have h4 : (Real.sqrt 2 - 1) / (Real.sqrt 2 + 1) = 3 - 2 * Real.sqrt 2 := by 
    field_simp [h3]
    nlinarith [h2, Real.sqrt_nonneg 2]

  have h5 : (10 - 7 * Real.sqrt 2) ^ ((1 : ℝ) / 3) / (10 + 7 * Real.sqrt 2) ^ ((1 : ℝ) / 3) = ( (10 - 7 * Real.sqrt 2) / (10 + 7 * Real.sqrt 2) ) ^ ((1 : ℝ) / 3) := by 
    rw [← Real.div_rpow]
    all_goals 
      nlinarith [show 0 ≤ (10 - 7 * Real.sqrt 2 : ℝ) by nlinarith [Real.sqrt_nonneg 2, h2, Real.sqrt_nonneg 2], show 0 ≤ (10 + 7 * Real.sqrt 2 : ℝ) by nlinarith [Real.sqrt_nonneg 2, h2, Real.sqrt_nonneg 2]]

  have h6 : ( (10 - 7 * Real.sqrt 2) / (10 + 7 * Real.sqrt 2) ) = (99 - 70 * Real.sqrt 2) := by
    have h8 : (10 + 7 * Real.sqrt 2) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 2, h2, h1]
    field_simp [h8]
    nlinarith [Real.sqrt_nonneg 2, h2, Real.sqrt_nonneg 2]

  have h7 : (99 - 70 * Real.sqrt 2) = (3 - 2 * Real.sqrt 2) ^ 3 := by 
    nlinarith [Real.sqrt_nonneg 2, h2, Real.sqrt_nonneg 2]

  have h8 : ( (99 - 70 * Real.sqrt 2) : ℝ ) ^ ((1 : ℝ) / 3) = (3 - 2 * Real.sqrt 2) := by
    rw [show (99 - 70 * Real.sqrt 2) = (3 - 2 * Real.sqrt 2) ^ 3 by nlinarith [Real.sqrt_nonneg 2, h2, Real.sqrt_nonneg 2] ]
    rw [show (( (3 - 2 * Real.sqrt 2) ^ 3 ) : ℝ) ^ ((1 : ℝ) / 3) = ( (3 - 2 * Real.sqrt 2) ) by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals 
        nlinarith [show 0 ≤ (3 - 2 * Real.sqrt 2 : ℝ) by nlinarith [Real.sqrt_nonneg 2, h1, h2, Real.sqrt_nonneg 2]]
    ]

  rw [h5]
  rw [h6]
  rw [h8]
  rw [h4]
  all_goals 
    nlinarith [Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]