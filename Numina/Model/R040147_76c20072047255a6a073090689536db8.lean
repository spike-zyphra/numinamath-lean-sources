import Mathlib

open Real

theorem algebra_232268 : 4 * (cos (π / 10))^2 - 1 = 1 / (4 * (sin (π / 10))^2) := by 
  have h1 : sin (π / 10) ^ 2 + cos (π / 10) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (π / 10)
  have h3 : (cos (π / 10)) ^ 2 = (5 + Real.sqrt 5) / 8 := by 
    have h4 : (cos (π / 10)) ^ 2 = (1 + cos (π / 5)) / 2 := by 
      have h5 : cos (π / 10) ^ 2 = (1 + cos (2 * (π / 10)) ) / 2 := by 
        rw [cos_sq]
        <;> ring_nf 
      rw [h5]
      have h7 : 2 * (π / 10) = π / 5 := by 
        ring_nf 
      rw [h7]
    have h7 : cos (π / 5) = (1 + Real.sqrt 5) / 4 := by 
      exact cos_pi_div_five 
    rw [h4, h7]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h4 : (sin (π / 10)) ^ 2 = (3 - Real.sqrt 5) / 8 := by 
    have h5 : sin (π / 10) ^ 2 = 1 - cos (π / 10) ^ 2 := by 
      have h7 : sin (π / 10) ^ 2 + cos (π / 10) ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq (π / 10)
      linarith 
    rw [h5, h3]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  rw [h3, h4]
  have h4' : Real.sqrt 5 ^ 2 = 5 := by
    exact Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  field_simp [(show 3 - Real.sqrt 5 ≠ 0 by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  ), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num)]
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), h4', Real.sqrt_nonneg 5, h3, h4]