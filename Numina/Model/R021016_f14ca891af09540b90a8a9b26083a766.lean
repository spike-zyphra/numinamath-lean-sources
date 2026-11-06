import Mathlib

open Real

theorem algebra_120823 : sqrt (4 + sqrt 7) - sqrt (4 - sqrt 7) - sqrt 2 ≤ 0 := by
  have h1 : sqrt (4 + sqrt 7) ≥ 0 := Real.sqrt_nonneg (4 + sqrt 7)
  have h2 : sqrt (4 - sqrt 7) ≥ 0 := Real.sqrt_nonneg (4 - sqrt 7)
  have h3 : sqrt (2 : ℝ) ≥ 0 := Real.sqrt_nonneg (2 : ℝ)
  have h4 : sqrt (4 + sqrt 7) - sqrt (4 - sqrt 7) ≤ sqrt 2 := by
    have h5 : (sqrt (4 + sqrt 7) - sqrt (4 - sqrt 7)) ^ 2 ≤ (sqrt 2) ^ 2 := by
      have h6 : (sqrt (4 + sqrt 7) - sqrt (4 - sqrt 7)) ^ 2 = 2 := by
        have h7 : (sqrt (4 + sqrt 7) - sqrt (4 - sqrt 7)) ^ 2 = (sqrt (4 + sqrt 7)) ^ 2 + (sqrt (4 - sqrt 7)) ^ 2 - 2 * (sqrt (4 + sqrt 7) * sqrt (4 - sqrt 7)) := by 
          ring
        rw [h7]
        have h8 : (sqrt (4 + sqrt 7)) ^ 2 = 4 + sqrt 7 := by
          rw [Real.sq_sqrt]
          positivity
        have h9 : (sqrt (4 - sqrt 7)) ^ 2 = 4 - sqrt 7 := by
          rw [Real.sq_sqrt]
          have h10 : sqrt 7 ≤ 4 := by
            nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
          nlinarith
        have h10 : sqrt (4 + sqrt 7) * sqrt (4 - sqrt 7) = 3 := by
          have h11 : sqrt (4 + sqrt 7) * sqrt (4 - sqrt 7) = sqrt ((4 + sqrt 7) * (4 - sqrt 7)) := by
            rw [← Real.sqrt_mul (by
              nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
            )]
          have h12 : (4 + sqrt 7) * (4 - sqrt 7) = 9 := by
            nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
          have h13 : sqrt ((4 + sqrt 7) * (4 - sqrt 7)) = 3 := by
            rw [h12]
            exact Real.sqrt_eq_cases.2 (by norm_num)
          rw [h11, h13]
        nlinarith [h8, h9, h10]
      have h10 : (sqrt (2 : ℝ)) ^ 2 = 2 := by 
        rw [Real.sq_sqrt]
        all_goals norm_num
      nlinarith [h6, h10, Real.sqrt_nonneg (4 + sqrt 7), Real.sqrt_nonneg (4 - sqrt 7), Real.sqrt_nonneg (2 : ℝ)]
    have h5' : sqrt (4 + sqrt 7) - sqrt (4 - sqrt 7) ≥ 0 := by
      have h6 : sqrt (4 + sqrt 7) ≥ sqrt (4 - sqrt 7) := by
        apply Real.sqrt_le_sqrt
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
      linarith
    nlinarith [Real.sqrt_nonneg (2 : ℝ), h5, h5']
  linarith [h4, Real.sqrt_nonneg (4 + sqrt 7), Real.sqrt_nonneg (4 - sqrt 7), Real.sqrt_nonneg 2]