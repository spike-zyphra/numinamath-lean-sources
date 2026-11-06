import Mathlib

theorem algebra_160538 : (54 * Real.sqrt 3 < 144 ∧ 54 * Real.sqrt 3 < 108 * Real.sqrt 6 - 108 * Real.sqrt 2) := by
  have h1 : 54 * Real.sqrt 3 < 144 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h2 : 54 * Real.sqrt 3 < 108 * Real.sqrt 6 - 108 * Real.sqrt 2 := by
    have h3 : Real.sqrt 6 > Real.sqrt 2 := by
      apply Real.sqrt_lt_sqrt
      all_goals norm_num
    have h4 : Real.sqrt 3 > 0 := by
      apply Real.sqrt_pos.mpr
      all_goals norm_num
    have h5 : Real.sqrt 6 > 0 := by
      apply Real.sqrt_pos.mpr
      all_goals norm_num
    have h6 : Real.sqrt 2 > 0 := by
      apply Real.sqrt_pos.mpr
      all_goals norm_num
    have h7 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    have h8 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h9 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, Real.sqrt_nonneg 2,
      mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2), 
      mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 6), 
      mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 6), 
      sq_nonneg (Real.sqrt 3 - (2 * Real.sqrt 6 - 2 * Real.sqrt 2)), 
      sq_nonneg (Real.sqrt 2 - Real.sqrt 3 / 2), 
      sq_nonneg (Real.sqrt 6 - 2 * Real.sqrt 2), 
      sq_pos_of_pos h4, sq_pos_of_pos h5, sq_pos_of_pos h6, 
      Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
      h3
    ]
  constructor
  · exact h1
  · exact h2