import Mathlib

theorem algebra_321250 : (Real.sqrt 3 + Real.sqrt 5) / (3 - Real.sqrt 6 - Real.sqrt 10 + Real.sqrt 15) = Real.sqrt 3 + Real.sqrt 2 := by 
  have h1 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num [Real.mul_self_sqrt, mul_assoc]
  
  have h2 : Real.sqrt 10 = Real.sqrt 2 * Real.sqrt 5 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num [Real.mul_self_sqrt, mul_assoc]

  have h3 : Real.sqrt 15 = Real.sqrt 3 * Real.sqrt 5 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num [Real.mul_self_sqrt, mul_assoc]

  have h4 : (3 - Real.sqrt 6 - Real.sqrt 10 + Real.sqrt 15) = (Real.sqrt 3 - Real.sqrt 2) * (Real.sqrt 3 + Real.sqrt 5) := by 
    rw [h1, h2, h3]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 5), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 5)]
  
  have h5 : Real.sqrt 3 + Real.sqrt 5 ≠ 0 := by 
    positivity
  
  have h6 : Real.sqrt 3 - Real.sqrt 2 ≠ 0 := by 
    -- Show sqrt(3) - sqrt(2) ≠ 0
    by_contra h
    have h7 : Real.sqrt 3 = Real.sqrt 2 := by linarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2]
    have h8 : (Real.sqrt 3) ^ 2 = (Real.sqrt 2) ^ 2 := by 
      rw [h7]
    -- norm_num at h8
    -- leads to 3 = 2
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg 2]

  rw [h4]
  field_simp [show Real.sqrt 3 - Real.sqrt 2 ≠ 0 by exact h6, show Real.sqrt 3 + Real.sqrt 5 ≠ 0 by exact h5]
  <;> ring_nf <;> norm_num
  <;> ring
  <;> norm_num
  all_goals nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]