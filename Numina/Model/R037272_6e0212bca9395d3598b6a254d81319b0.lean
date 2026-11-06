import Mathlib

theorem algebra_187435 : Real.cos (Real.pi / 18) ^ 2 + Real.cos (5 * Real.pi / 18) ^ 2 - Real.sin (4 * Real.pi / 18) * Real.sin (8 * Real.pi / 18) = 3 / 4 := by
  have h1 : Real.cos (5 * Real.pi / 18) = 1 / 2 * Real.cos (Real.pi / 18) + Real.sqrt 3 / 2 * Real.sin (Real.pi / 18) := by
    have h2 : 5 * Real.pi / 18 = Real.pi / 3 - Real.pi / 18 := by 
      linarith [Real.pi_pos]
    rw [h2]
    rw [Real.cos_sub]
    have h3 : Real.cos (Real.pi / 3) = 1 / 2 := by
      rw [Real.cos_pi_div_three]
    have h4 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := by 
      rw [Real.sin_pi_div_three]
    simp [h3, h4]
    <;> ring
  have h2 : Real.sin (4 * Real.pi / 18) = 1 / 2 * Real.cos (Real.pi / 18) + Real.sqrt 3 / 2 * Real.sin (Real.pi / 18) := by
    have h3 : 4 * Real.pi / 18 = Real.pi / 6 + Real.pi / 18 := by
      linarith [Real.pi_pos]
    rw [h3]
    rw [Real.sin_add]
    have h4 : Real.sin (Real.pi / 6) = 1 / 2 := by 
      rw [Real.sin_pi_div_six]
    have h5 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := by 
      rw [Real.cos_pi_div_six]
    simp [h4, h5]
    <;> ring
  have h3 : Real.sin (8 * Real.pi / 18) = Real.cos (Real.pi / 18) := by 
    have h4 : 8 * Real.pi / 18 = Real.pi / 2 - Real.pi / 18 := by 
      linarith [Real.pi_pos]
    rw [h4]
    rw [Real.sin_pi_div_two_sub]
  rw [h1, h2, h3]
  have h4 : Real.sin (Real.pi / 18) ^ 2 + Real.cos (Real.pi / 18) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (Real.pi / 18)
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sin (Real.pi / 18) - Real.cos (Real.pi / 18)), sq_nonneg (Real.sin (Real.pi / 18) + Real.cos (Real.pi / 18)), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]