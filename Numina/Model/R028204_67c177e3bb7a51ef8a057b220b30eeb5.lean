import Mathlib

open Real

theorem algebra_260228 : (sqrt 2 / (sqrt 2 + sqrt 3 - sqrt 5)) = (3 + sqrt 6 + sqrt 15) / 6 := by
  have h1 : 0 < (2 : ℝ) := by norm_num
  have h2 : 0 < (3 : ℝ) := by norm_num
  have h3 : 0 < (5 : ℝ) := by norm_num
  have h4 : sqrt 2 > 0 := by positivity
  have h5 : sqrt 3 > 0 := by positivity
  have h6 : sqrt 5 > 0 := by positivity
  have h7 : sqrt 6 = sqrt 2 * sqrt 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h8 : sqrt 15 = sqrt 3 * sqrt 5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h10 : sqrt 2 + sqrt 3 - sqrt 5 ≠ 0 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, 
            Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
            sq_pos_of_pos (show sqrt 2 > 0 by positivity), 
            sq_pos_of_pos (show sqrt 3 > 0 by positivity), 
            sq_pos_of_pos (show sqrt 5 > 0 by positivity), 
            Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ (3 : ℝ)), 
            Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ (5 : ℝ)), 
            Real.sqrt_le_sqrt (by norm_num : (3 : ℝ) ≤ (5 : ℝ)), 
            sq_nonneg (sqrt 2 - sqrt 3), sq_nonneg (sqrt 2 - sqrt 5), sq_nonneg (sqrt 3 - sqrt 5), 
            Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
            Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
            Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  rw [h7, h8]
  field_simp [h10]
  nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
          sq_nonneg (sqrt 2 - sqrt 3), sq_nonneg (sqrt 2 - sqrt 5), sq_nonneg (sqrt 3 - sqrt 5), 
          Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3), 
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 5), 
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 5)]