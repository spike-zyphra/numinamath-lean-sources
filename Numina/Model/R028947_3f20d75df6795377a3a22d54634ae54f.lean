import Mathlib

open Real

theorem algebra_1481 : sqrt (6 - sqrt 35) + sqrt (6 + sqrt 35) = sqrt 14 := by
  have h1 : sqrt (6 - sqrt 35) + sqrt (6 + sqrt 35) ≥ 0 := by
    positivity
  have h2 : (sqrt (6 - sqrt 35) + sqrt (6 + sqrt 35)) ^ 2 = 14 := by
    have h3 : (sqrt (6 - sqrt 35) + sqrt (6 + sqrt 35)) ^ 2
        = (sqrt (6 - sqrt 35)) ^ 2 + (sqrt (6 + sqrt 35)) ^ 2 + 2 * (sqrt (6 - sqrt 35) * sqrt (6 + sqrt 35)) := by
      ring
    rw [h3]
    have h4 : (sqrt (6 - sqrt 35)) ^ 2 = 6 - sqrt 35 := by
      rw [Real.sq_sqrt]
      nlinarith [Real.sqrt_nonneg 35, Real.sq_sqrt (show 0 ≤ (35 : ℝ) by norm_num)]
    have h5 : (sqrt (6 + sqrt 35)) ^ 2 = 6 + sqrt 35 := by
      rw [Real.sq_sqrt]
      nlinarith [Real.sqrt_nonneg 35, Real.sq_sqrt (show 0 ≤ (35 : ℝ) by norm_num)]
    have h6 : sqrt (6 - sqrt 35) * sqrt (6 + sqrt 35) = 1 := by
      have h7 : sqrt (6 - sqrt 35) * sqrt (6 + sqrt 35) = sqrt ((6 - sqrt 35) * (6 + sqrt 35)) := by
        rw [← Real.sqrt_mul (by
          nlinarith [Real.sqrt_nonneg 35, Real.sq_sqrt (show 0 ≤ (35 : ℝ) by norm_num)]
        )]
      rw [h7]
      have h8 : (6 - sqrt 35) * (6 + sqrt 35) = 1 := by
        nlinarith [Real.sqrt_nonneg 35, Real.sq_sqrt (show 0 ≤ (35 : ℝ) by norm_num)]
      rw [h8]
      all_goals simp
    rw [h4, h5, h6]
    all_goals nlinarith [Real.sqrt_nonneg 35, Real.sq_sqrt (show 0 ≤ (35 : ℝ) by norm_num)]
  have h3 : sqrt ((sqrt (6 - sqrt 35) + sqrt (6 + sqrt 35)) ^ 2) = sqrt (14) := by
    rw [h2]
  have h4 : sqrt ((sqrt (6 - sqrt 35) + sqrt (6 + sqrt 35)) ^ 2) = sqrt (6 - sqrt 35) + sqrt (6 + sqrt 35) := by
    rw [Real.sqrt_sq (show 0 ≤ sqrt (6 - sqrt 35) + sqrt (6 + sqrt 35) by positivity)]
  rw [h4] at h3
  linarith