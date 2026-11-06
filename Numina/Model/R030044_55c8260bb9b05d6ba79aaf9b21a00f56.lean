import Mathlib

open Real

theorem inequalities_183119 :
    sqrt 7 + sqrt 10 < sqrt 3 + sqrt 19 := by
  have h2 : sqrt 7 ≥ 0 := Real.sqrt_nonneg 7
  have h3 : sqrt 10 ≥ 0 := Real.sqrt_nonneg 10
  have h4 : sqrt 3 ≥ 0 := Real.sqrt_nonneg 3
  have h5 : sqrt 19 ≥ 0 := Real.sqrt_nonneg 19
  have h6 : (sqrt 7 + sqrt 10) ^ 2 < (sqrt 3 + sqrt 19) ^ 2 := by
    have h7 : (sqrt 7 + sqrt 10) ^ 2 = (sqrt 7) ^ 2 + (sqrt 10) ^ 2 + 2 * (sqrt 7 * sqrt 10) := by ring
    have h8 : (sqrt 3 + sqrt 19) ^ 2 = (sqrt 3) ^ 2 + (sqrt 19) ^ 2 + 2 * (sqrt 3 * sqrt 19) := by ring
    rw [h7, h8]
    have h9 : (sqrt 7) ^ 2 = 7 := Real.sq_sqrt (show (7 : ℝ) ≥ 0 by norm_num)
    have h10 : (sqrt 10) ^ 2 = 10 := Real.sq_sqrt (show (10 : ℝ) ≥ 0 by norm_num)
    have h11 : (sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)
    have h12 : (sqrt 19) ^ 2 = 19 := Real.sq_sqrt (show (19 : ℝ) ≥ 0 by norm_num)
    rw [h9, h10, h11, h12]
    have h13 : sqrt 7 * sqrt 10 = sqrt 70 := by
      have h14 : sqrt 7 * sqrt 10 = sqrt (7 * 10) := by
        rw [← Real.sqrt_mul (by norm_num)]
      rw [h14]
      all_goals norm_num
    have h14 : sqrt 3 * sqrt 19 = sqrt 57 := by
      have h15 : sqrt 3 * sqrt 19 = sqrt (3 * 19) := by
        rw [← Real.sqrt_mul (by norm_num)]
      rw [h15]
      all_goals norm_num
    rw [h13, h14]
    have h15 : sqrt 70 < sqrt 57 + 5 / 2 := by
      nlinarith [Real.sqrt_nonneg 70, Real.sqrt_nonneg 57, 
        sq_nonneg (sqrt 70 - sqrt 57), 
        sq_nonneg (sqrt 70 - 5 / 2), 
        Real.sq_sqrt (show (70 : ℝ) ≥ 0 by norm_num), 
        Real.sq_sqrt (show (57 : ℝ) ≥ 0 by norm_num), 
        mul_nonneg (Real.sqrt_nonneg 70) (Real.sqrt_nonneg 57), 
        sq_nonneg (sqrt 57 - sqrt 70)
      ]
    nlinarith [Real.sqrt_nonneg 70, Real.sqrt_nonneg 57, 
      sq_nonneg (sqrt 70 - sqrt 57), 
      Real.sq_sqrt (show (70 : ℝ) ≥ 0 by norm_num), 
      Real.sq_sqrt (show (57 : ℝ) ≥ 0 by norm_num), 
      h15, 
      mul_nonneg (Real.sqrt_nonneg 70) (Real.sqrt_nonneg 57)
    ]
  have h7 : sqrt 7 + sqrt 10 ≥ 0 := by linarith [h2, h3]
  have h8 : sqrt 3 + sqrt 19 ≥ 0 := by linarith [h4, h5]
  nlinarith [Real.sqrt_nonneg 7, Real.sqrt_nonneg 10, Real.sqrt_nonneg 3, Real.sqrt_nonneg 19, h6, h7, h8, 
          sq_nonneg (sqrt 7 + sqrt 10 - (sqrt 3 + sqrt 19))
        ]