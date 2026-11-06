import Mathlib

theorem algebra_146034 : (4 + 2 * √6) / ((1 + √2) + √3) = -1 + √2 + √3 := by
  have h1 : (4 + 2 * √6 : ℝ) = ((-1 + √2 + √3) : ℝ) * ((1 + √2) + √3 : ℝ) := by 
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (6 : ℝ), 
            Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
            Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
            Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num),
            Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 : ℝ) by norm_num),
            Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (6 : ℝ) by norm_num),
            Real.sqrt_le_sqrt (show (3 : ℝ) ≤ (6 : ℝ) by norm_num),
            mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3), 
            sq_nonneg (√2 - √3), sq_nonneg (√2 + √3),
            Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
            Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
            sq_nonneg (√6), Real.sqrt_nonneg (6 : ℝ)]
  have h2 : ((1 + √2) + √3 : ℝ) ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
          Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          sq_nonneg (√2 - √3), sq_nonneg (√2 + √3)
        ]
  rw [h1]
  field_simp [h2]
  <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (6 : ℝ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]