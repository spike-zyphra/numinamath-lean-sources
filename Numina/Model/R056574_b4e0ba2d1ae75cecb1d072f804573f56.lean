import Mathlib

open Real

theorem algebra_185140 : (3 + sqrt 2 + sqrt 3) / (3 - sqrt 2 - sqrt 3) =
    -(4 + 3 * sqrt 2) * (5 + 3 * sqrt 3) / 2 := by
  have h1 : (3 - sqrt 2 - sqrt 3) ≠ 0 := by
    by_contra h
    have h2 : sqrt 2 + sqrt 3 = 3 := by linarith
    have h3 : (sqrt 2 + sqrt 3) ^ 2 = (3 : ℝ) ^ 2 := by
      rw [h2]
      all_goals nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ)]
    have h4 : (sqrt 2 + sqrt 3) ^ 2 = (sqrt 2) ^ 2 + (sqrt 3) ^ 2 + 2 * (sqrt 2 * sqrt 3) := by 
      nlinarith 
    have h5 : (sqrt 2 + sqrt 3) ^ 2 = 5 + 2 * (sqrt 2 * sqrt 3) := by 
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h6 : (sqrt 2 * sqrt 3) = (sqrt 6 : ℝ) := by
      have h11 : sqrt 6 = sqrt (2 * 3) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
      have h9b : sqrt 2 * sqrt 3 = sqrt (2 * 3) := by 
        rw [← Real.sqrt_mul (by norm_num)]
        all_goals nlinarith
      rw [h9b, h11]
      all_goals nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
    have h7 : (sqrt 6 : ℝ) ^ 2 = (6 : ℝ) := by 
      rw [Real.sq_sqrt]
      norm_num
    nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h6, h5]
  field_simp [h1]
  have h7 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
  have h8 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (sqrt 2 - 1), sq_nonneg (sqrt 3 - 1), mul_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ))) (Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)))]