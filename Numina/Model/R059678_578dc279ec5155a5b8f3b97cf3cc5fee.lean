import Mathlib

theorem algebra_199610 : (3 + √8) ^ ((1 : ℝ) / 2023) + (3 - √8) ^ ((1 : ℝ) / 2023) > 2 := by 
  have h2 : Real.sqrt 8 ^ 2 = 8 := by 
    rw [Real.sq_sqrt]
    norm_num
  have h3 : 0 < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have h4 : 0 < (3 + Real.sqrt 8) := by nlinarith [Real.sqrt_nonneg 8, Real.sqrt_pos.mpr (show (0 : ℝ) < (8 : ℝ) by norm_num)]
  have h5 : 0 < (3 - Real.sqrt 8) := by
    nlinarith [Real.sqrt_nonneg 8, Real.sqrt_pos.mpr (show (0 : ℝ) < (8 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num), show Real.sqrt 8 < (3 : ℝ) by
      rw [Real.sqrt_lt] <;> norm_num
      <;> nlinarith
    ]
  have h6 : (3 + Real.sqrt 8) * (3 - Real.sqrt 8) = 1 := by 
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)]
  have h7 : ((3 + Real.sqrt 8) * (3 - Real.sqrt 8)) ^ ((1 : ℝ) / 2023) = 1 := by 
    rw [h6]
    norm_num
  have h8 : ((3 + Real.sqrt 8) * (3 - Real.sqrt 8)) ^ ((1 : ℝ) / 2023) = (3 + Real.sqrt 8) ^ ((1 : ℝ) / 2023) * (3 - Real.sqrt 8) ^ ((1 : ℝ) / 2023) := by 
    rw [← Real.mul_rpow]
    all_goals 
      nlinarith [Real.sqrt_nonneg 8]
  have h9 : (3 + Real.sqrt 8) ^ ((1 : ℝ) / 2023) * (3 - Real.sqrt 8) ^ ((1 : ℝ) / 2023) = 1 := by 
    linarith [h7, h8]
  have h13 : (3 + Real.sqrt 8) ^ ((1 : ℝ) / 2023) > (1 : ℝ) := by
    have h9 : (1 : ℝ) < (3 + Real.sqrt 8) := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (8 : ℝ) by norm_num), Real.sqrt_nonneg 8]
    have h10 : (3 + Real.sqrt 8) ^ ((1 : ℝ) / 2023) > (1 : ℝ) ^ ((1 : ℝ) / 2023) := by
      apply Real.rpow_lt_rpow
      · linarith
      · linarith
      · norm_num
    have h11 : (1 : ℝ) ^ ((1 : ℝ) / 2023) = 1 := by 
      simp
    linarith [h11, h10]
  have h14 : (3 - Real.sqrt 8) ^ ((1 : ℝ) / 2023) < (1 : ℝ) := by 
    have h9 : (3 - Real.sqrt 8) < (1 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (8 : ℝ) by norm_num), Real.sqrt_nonneg 8]
    have h10 : (3 - Real.sqrt 8) ^ ((1 : ℝ) / 2023) < (1 : ℝ) ^ ((1 : ℝ) / 2023) := by
      apply Real.rpow_lt_rpow
      · linarith
      · linarith
      · norm_num
    have h11 : (1 : ℝ) ^ ((1 : ℝ) / 2023) = 1 := by 
      simp
    linarith [h11, h10]
  nlinarith [sq_nonneg ((3 + Real.sqrt 8) ^ ((1 : ℝ) / 2023) - (3 - Real.sqrt 8) ^ ((1 : ℝ) / 2023)), 
    h9, Real.rpow_pos_of_pos h4 (1 / 2023), Real.rpow_pos_of_pos h5 (1 / 2023), h13, h14
  ]