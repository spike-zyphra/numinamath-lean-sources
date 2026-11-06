import Mathlib

open Real Set

theorem inequalities_178936 (x : ℝ) :
    2 ^ sin x ^ 2 + 2 ^ cos x ^ 2 ≥ 2 * sqrt 2 := by
  have h1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h2 : (2 : ℝ) ^ (sin x ^ 2) > 0 := by positivity
  have h3 : (2 : ℝ) ^ (cos x ^ 2) > 0 := by positivity
  have h4 : sin x ^ 2 ≥ 0 := by
    have : sin x ^ 2 ≥ 0 := by positivity
    linarith
  have h5 : cos x ^ 2 ≥ 0 := by
    have : cos x ^ 2 ≥ 0 := by positivity
    linarith
  have h8 : (2 : ℝ) ^ sin x ^ 2 * (2 : ℝ) ^ cos x ^ 2 = 2 := by
    have h9 : (2 : ℝ) ^ sin x ^ 2 * (2 : ℝ) ^ cos x ^ 2 = (2 : ℝ) ^ (sin x ^ 2 + cos x ^ 2) := by
      rw [← Real.rpow_add]
      ring_nf
      all_goals
        try linarith
        all_goals norm_num
    rw [h9, h1]
    all_goals
      norm_num
  have h10 : (2 : ℝ) ^ sin x ^ 2 + (2 : ℝ) ^ cos x ^ 2 ≥ 2 * Real.sqrt 2 := by
    nlinarith [sq_nonneg ((2 : ℝ) ^ sin x ^ 2 - (2 : ℝ) ^ cos x ^ 2), sq_nonneg ((2 : ℝ) ^ sin x ^ 2 - Real.sqrt 2), sq_nonneg ((2 : ℝ) ^ cos x ^ 2 - Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.rpow_nonneg (show 0 ≤ (2 : ℝ) by norm_num) (sin x ^ 2), Real.rpow_nonneg (show 0 ≤ (2 : ℝ) by norm_num) (cos x ^ 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_nonneg (Real.rpow_nonneg (show 0 ≤ (2 : ℝ) by norm_num) (sin x ^ 2)) (Real.rpow_nonneg (show 0 ≤ (2 : ℝ) by norm_num) (cos x ^ 2)), h8]
  linarith
  all_goals norm_num