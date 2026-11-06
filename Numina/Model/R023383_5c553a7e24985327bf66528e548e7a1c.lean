import Mathlib

theorem algebra_95903 : (|Real.sqrt 65 - Real.sqrt 63 - 0.13| < 0.01) := by
  have h1 : Real.sqrt 65 > 8 := by
    have h4 : Real.sqrt 64 = (8 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt 65 > Real.sqrt 64 := by
      apply Real.sqrt_lt_sqrt
      all_goals norm_num
    linarith [h4, h2]

  have h1' : Real.sqrt 63 < 8 := by 
    have h4 : Real.sqrt 64 = (8 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h5 : Real.sqrt 63 < Real.sqrt 64 := by
      apply Real.sqrt_lt_sqrt
      all_goals norm_num
    nlinarith [h4, h5]

  have h5 : Real.sqrt 65 - Real.sqrt 63 > (0.12 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 65, Real.sqrt_nonneg 63, sq_nonneg (Real.sqrt 65 - 8), sq_nonneg (Real.sqrt 63 - 8), 
      Real.sq_sqrt (show 0 ≤ (65 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (63 : ℝ) by norm_num), 
      mul_nonneg (Real.sqrt_nonneg 65) (Real.sqrt_nonneg 63), 
      show Real.sqrt 65 > Real.sqrt 63 by apply Real.sqrt_lt_sqrt; all_goals norm_num
    ]

  have h6 : Real.sqrt 65 - Real.sqrt 63 < (0.14 : ℝ) := by 
    nlinarith [Real.sqrt_nonneg 65, Real.sqrt_nonneg 63, sq_nonneg (Real.sqrt 65 - 8), sq_nonneg (Real.sqrt 63 - 8), 
      Real.sq_sqrt (show 0 ≤ (65 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (63 : ℝ) by norm_num), 
      mul_nonneg (Real.sqrt_nonneg 65) (Real.sqrt_nonneg 63), 
      show Real.sqrt 65 > Real.sqrt 63 by apply Real.sqrt_lt_sqrt; all_goals norm_num
    ]

  have h7 : Real.sqrt 65 - Real.sqrt 63 - 0.13 > (-0.01 : ℝ) := by 
    nlinarith

  have h8 : Real.sqrt 65 - Real.sqrt 63 - 0.13 < (0.01 : ℝ) := by 
    nlinarith

  rw [abs_lt]
  constructor <;> nlinarith [h7, h8]