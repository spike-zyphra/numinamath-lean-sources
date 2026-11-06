import Mathlib

open Real

theorem algebra_157087 : tan (π / 12) + 2 * sqrt 2 * sin (π / 12) = 1 := by
  have h1 : sin (π / 12) = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
    have h2 : sin (π / 12) = sin ( (π / 3) - (π / 4) ) := by 
      ring_nf
    rw [h2]
    have h3 : sin ((π / 3) - (π / 4)) = sin (π / 3) * cos (π / 4) - cos (π / 3) * sin (π / 4) := by 
      rw [sin_sub]
    rw [h3]
    have h4 : sin (π / 3) = Real.sqrt 3 / 2 := by 
      exact sin_pi_div_three
    have h5 : cos (π / 3) = 1 / 2 := by 
      exact cos_pi_div_three
    have h6 : sin (π / 4) = Real.sqrt 2 / 2 := by 
      have h : sin (π / 4) = Real.sqrt 2 / 2 := by 
        rw [sin_pi_div_four]
      linarith
    have h7 : cos (π / 4) = Real.sqrt 2 / 2 := by 
      have h : cos (π / 4) = Real.sqrt 2 / 2 := by 
        rw [cos_pi_div_four]
      linarith
    rw [h4, h5, h6, h7]
    have h8 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by 
      have h9 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt (3 * 2) := by 
        rw [← Real.sqrt_mul (by norm_num)]
      have h10 : Real.sqrt (3 * 2) = Real.sqrt 6 := by 
        norm_num
      rw [h9, h10]
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
  
  have h2 : cos (π / 12) = (Real.sqrt 2 + Real.sqrt 6) / 4 := by 
    have h2 : cos (π / 12) = cos ( (π / 3) - (π / 4) ) := by 
      ring_nf
    rw [h2]
    have h3 : cos ((π / 3) - (π / 4)) = cos (π / 3) * cos (π / 4) + sin (π / 3) * sin (π / 4) := by 
      rw [cos_sub]
    rw [h3]
    have h4 : cos (π / 3) = 1 / 2 := by 
      exact cos_pi_div_three
    have h5 : sin (π / 3) = Real.sqrt 3 / 2 := by 
      exact sin_pi_div_three
    have h6 : cos (π / 4) = Real.sqrt 2 / 2 := by 
      have h : cos (π / 4) = Real.sqrt 2 / 2 := by 
        rw [cos_pi_div_four]
      linarith
    have h7 : sin (π / 4) = Real.sqrt 2 / 2 := by 
      have h : sin (π / 4) = Real.sqrt 2 / 2 := by 
        rw [sin_pi_div_four]
      linarith
    rw [h4, h5, h6, h7]
    have h8 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by 
      have h9 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt (3 * 2) := by 
        rw [← Real.sqrt_mul (by norm_num)]
      have h10 : Real.sqrt (3 * 2) = Real.sqrt 6 := by 
        norm_num
      rw [h9, h10]
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
  
  have h3 : tan (π / 12) = 2 - Real.sqrt 3 := by 
    rw [tan_eq_sin_div_cos, h1, h2]
    have h5 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by 
      have h1 : Real.sqrt 6 = Real.sqrt (2 * 3) := by 
        norm_num
      have h2 : Real.sqrt (2 * 3) = Real.sqrt 2 * Real.sqrt 3 := by 
        rw [Real.sqrt_mul (by norm_num)]
      rw [h1, h2]
    rw [show Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 by linarith [h5]]
    field_simp [(show Real.sqrt 2 ≠ 0 by 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    )]
    <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
  
  rw [h3]
  rw [h1]
  have h5 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by 
    have h1 : Real.sqrt 6 = Real.sqrt (2 * 3) := by 
      norm_num
    have h2 : Real.sqrt (2 * 3) = Real.sqrt 2 * Real.sqrt 3 := by 
      rw [Real.sqrt_mul (by norm_num)]
    rw [h1, h2]
  rw [show Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 by linarith [h5]]
  field_simp [(show Real.sqrt 2 > 0 by 
    apply Real.sqrt_pos.mpr
    linarith
  )]
  <;> nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (4 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (4 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (Real.sqrt_nonneg (3 : ℝ)), sq_nonneg (Real.sqrt 2 - Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]