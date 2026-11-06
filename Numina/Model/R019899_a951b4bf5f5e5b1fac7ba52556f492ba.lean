import Mathlib

open Real

theorem algebra_4192 :
    (sqrt 2 + sqrt 3 + sqrt 5) * (sqrt 2 + sqrt 3 - sqrt 5) *
    (sqrt 2 - sqrt 3 + sqrt 5) * (-sqrt 2 + sqrt 3 + sqrt 5) = 24 := by
  have h1 : sqrt 2 ^ 2 = 2 := by
    exact Real.sq_sqrt (by norm_num)
  have h2 : sqrt 3 ^ 2 = 3 := by
    exact Real.sq_sqrt (by norm_num)
  have h3 : sqrt 5 ^ 2 = 5 := by
    exact Real.sq_sqrt (by norm_num)
  have h4 : (sqrt 2 + sqrt 3 + sqrt 5) * (sqrt 2 + sqrt 3 - sqrt 5) = 2 * sqrt 6 := by
    have h5 : (sqrt 2 + sqrt 3) ^ 2 = 5 + 2 * sqrt 6 := by
      have h6 : sqrt 2 * sqrt 3 = sqrt 6 := by
        have h7 : sqrt 2 * sqrt 3 = sqrt (2 * 3) := by
          rw [← Real.sqrt_mul (by norm_num)]
        rw [h7]
        all_goals norm_num
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)
        ]
    calc
      (sqrt 2 + sqrt 3 + sqrt 5) * (sqrt 2 + sqrt 3 - sqrt 5)
          = (sqrt 2 + sqrt 3) ^ 2 - (sqrt 5) ^ 2 := by ring
      _ = (5 + 2 * sqrt 6) - (sqrt 5) ^ 2 := by rw [h5]
      _ = (5 + 2 * sqrt 6) - 5 := by rw [h3]
      _ = 2 * sqrt 6 := by linarith
  have h5 : (sqrt 2 - sqrt 3 + sqrt 5) * (-sqrt 2 + sqrt 3 + sqrt 5) = 2 * sqrt 6 := by
    have h6 : sqrt 6 = sqrt 2 * sqrt 3 := by
      have h7 : sqrt 6 = sqrt (2 * 3) := by
        norm_num [Real.sqrt_eq_iff_sq_eq]
      rw [h7, Real.sqrt_mul (by norm_num)]
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
        Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, 
        sq_nonneg (sqrt 2 - sqrt 3), sq_nonneg (sqrt 2 - sqrt 5), sq_nonneg (sqrt 3 - sqrt 5), 
        sq_nonneg (sqrt 2 * sqrt 3 - sqrt 2 * sqrt 5), sq_nonneg (sqrt 3 * sqrt 5 - sqrt 2 * sqrt 5)
       ]
  calc
    (sqrt 2 + sqrt 3 + sqrt 5) * (sqrt 2 + sqrt 3 - sqrt 5) * (sqrt 2 - sqrt 3 + sqrt 5) * (-sqrt 2 + sqrt 3 + sqrt 5)
        = ((sqrt 2 + sqrt 3 + sqrt 5) * (sqrt 2 + sqrt 3 - sqrt 5)) * ((sqrt 2 - sqrt 3 + sqrt 5) * (-sqrt 2 + sqrt 3 + sqrt 5)) := by ring
    _ = (2 * sqrt 6) * (2 * sqrt 6) := by rw [h4, h5]
    _ = 4 * (sqrt 6) ^ 2 := by ring
    _ = 4 * (6 : ℝ) := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    _ = (24 : ℝ) := by norm_num