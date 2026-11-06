import Mathlib

open Real

theorem algebra_3215 : (sqrt 28 + sqrt 20) * (sqrt 45 - sqrt 63) = -12 := by
  have h1 : sqrt 28 = 2 * sqrt 7 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h2 : sqrt 20 = 2 * sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h3 : sqrt 45 = 3 * sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h4 : sqrt 63 = 3 * sqrt 7 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  rw [h1, h2, h3, h4]
  nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 7,
          Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num),
          Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num),
          Real.mul_self_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num),
          Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (0 : ℝ) < (5 : ℝ)), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < (7 : ℝ) by norm_num : (0 : ℝ) < (7 : ℝ)), 
          mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 7), 
          sq_nonneg (sqrt 5 - sqrt 7), 
          sq_nonneg (sqrt 7 + sqrt 5), 
          sq_nonneg (sqrt 5 + sqrt 7),
          mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 7)
          ]