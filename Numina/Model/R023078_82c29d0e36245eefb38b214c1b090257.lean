import Mathlib

open Real

theorem inequalities_189829 : sqrt 5 + sqrt 8 < sqrt 6 + sqrt 7 := by
  have h1 : sqrt 5 ≥ 0 := by positivity
  have h2 : sqrt 8 ≥ 0 := by positivity
  have h3 : sqrt 6 ≥ 0 := by positivity
  have h4 : sqrt 7 ≥ 0 := by positivity
  have h5 : (sqrt 5 + sqrt 8) ^ 2 < (sqrt 6 + sqrt 7) ^ 2 := by
    have h10 : (sqrt 5 + sqrt 8) ^ 2 = (sqrt 5) ^ 2 + (sqrt 8) ^ 2 + 2 * (sqrt 5 * sqrt 8) := by ring
    have h11 : (sqrt 6 + sqrt 7) ^ 2 = (sqrt 6) ^ 2 + (sqrt 7) ^ 2 + 2 * (sqrt 6 * sqrt 7) := by ring
    rw [h10, h11]
    have h6 : (sqrt 5 : ℝ) ^ 2 = 5 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    have h7 : (sqrt 8 : ℝ) ^ 2 = 8 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    have h8 : (sqrt 6 : ℝ) ^ 2 = 6 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    have h9 : (sqrt 7 : ℝ) ^ 2 = 7 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    rw [h6, h7, h8, h9]
    have h8 : sqrt 5 * sqrt 8 = sqrt 40 := by
      have h1 : sqrt 5 * sqrt 8 = sqrt (5 * (8 : ℝ)) := by
        rw [← Real.sqrt_mul (by norm_num)]
      have h2 : sqrt (5 * (8 : ℝ)) = sqrt 40 := by
        norm_num
      rw [h1, h2]
    have h9 : sqrt 6 * sqrt 7 = sqrt 42 := by
      have h1 : sqrt 6 * sqrt 7 = sqrt (6 * (7 : ℝ)) := by
        rw [← Real.sqrt_mul (by norm_num)]
      have h2 : sqrt (6 * (7 : ℝ)) = sqrt 42 := by
        norm_num
      rw [h1, h2]
    have h10 : sqrt 40 < sqrt 42 := by
      apply Real.sqrt_lt_sqrt
      all_goals norm_num
    have h11 : sqrt 5 * sqrt 8 < sqrt 6 * sqrt 7 := by
      nlinarith [h8, h9, h10, Real.sqrt_nonneg 40, Real.sqrt_nonneg 42]
    nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 8, Real.sqrt_nonneg 6, Real.sqrt_nonneg 7, h11]
  have h6 : 0 ≤ (sqrt 5 : ℝ) + (sqrt 8 : ℝ) := by positivity
  have h7 : 0 ≤ (sqrt 6 : ℝ) + (sqrt 7 : ℝ) := by positivity
  nlinarith [h5, Real.sqrt_nonneg 5, Real.sqrt_nonneg 8, Real.sqrt_nonneg 6, Real.sqrt_nonneg 7]