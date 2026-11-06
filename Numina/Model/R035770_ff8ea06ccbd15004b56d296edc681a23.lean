import Mathlib

open Real

theorem algebra_299257 : sqrt (sqrt (2 + sqrt 3) + sqrt (2 - sqrt 3)) = 6 ^ ((1 : ℝ) / 4) := by
  have h1 : sqrt (2 + sqrt 3) + sqrt (2 - sqrt 3) = Real.sqrt 6 := by
    have h2 : (sqrt (2 + sqrt 3) + sqrt (2 - sqrt 3)) ^ 2 = 6 := by
      have h3 : (sqrt (2 + sqrt 3) + sqrt (2 - sqrt 3)) ^ 2 =
        (sqrt (2 + sqrt 3)) ^ 2 + (sqrt (2 - sqrt 3)) ^ 2 + 2 * (sqrt (2 + sqrt 3) * sqrt (2 - sqrt 3)) := by
        ring
      rw [h3]
      have h4 : (sqrt (2 + sqrt 3)) ^ 2 = 2 + sqrt 3 := by
        exact Real.sq_sqrt (by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
        )
      have h5 : (sqrt (2 - sqrt 3)) ^ 2 = 2 - sqrt 3 := by
        exact Real.sq_sqrt (by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
        )
      have h6 : sqrt (2 + sqrt 3) * sqrt (2 - sqrt 3) = 1 := by
        have h7 : sqrt (2 + sqrt 3) * sqrt (2 - sqrt 3) = sqrt ((2 + sqrt 3) * (2 - sqrt 3)) := by
          rw [← Real.sqrt_mul (by
            nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
          )]
        rw [h7]
        have h8 : (2 + sqrt 3) * (2 - sqrt 3) = 1 := by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
        rw [h8]
        simp
      rw [h4, h5, h6]
      all_goals nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h7 : 0 ≤ sqrt (2 + sqrt 3) + sqrt (2 - sqrt 3) := by
      positivity
    have h8 : 0 ≤ (Real.sqrt 6 : ℝ) := by
      positivity
    nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have h3 : sqrt (sqrt (2 + sqrt 3) + sqrt (2 - sqrt 3)) = sqrt (Real.sqrt 6) := by
    rw [h1]
  rw [h3]
  have h4 : sqrt (Real.sqrt 6) = (6 : ℝ) ^ ((1 : ℝ) / 4) := by
    have h6 : sqrt (Real.sqrt 6) = sqrt (( (6 : ℝ) ^ ((1 : ℝ) / 2) ) ) := by
      have h7 : ( (6 : ℝ) ^ ((1 : ℝ) / 2) ) = Real.sqrt 6 := by
        rw [Real.sqrt_eq_rpow]
      rw [h7]
    have h7 : sqrt (( (6 : ℝ) ^ ((1 : ℝ) / 2) ) ) = ( (6 : ℝ) ^ ((1 : ℝ) / 2) ) ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
      all_goals linarith
    have h8 : ( (6 : ℝ) ^ ((1 : ℝ) / 2) ) ^ ((1 : ℝ) / 2) = (6 : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_mul]
      ring
      all_goals norm_num
    rw [h6, h7, h8]
  exact h4