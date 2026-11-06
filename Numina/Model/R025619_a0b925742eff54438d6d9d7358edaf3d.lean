import Mathlib

open Real

theorem calculus_22407 : Real.cos (Real.pi / 12) = (Real.sqrt 2 + Real.sqrt 6) / 4 := by
  have h1 : Real.cos (Real.pi / 12) = Real.cos (Real.pi / 4 - Real.pi / 6) := by
    ring_nf
  rw [h1]
  rw [cos_sub]
  have h2 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [cos_pi_div_four]
  have h3 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [sin_pi_div_four]
  have h4 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
    rw [cos_pi_div_six]
  have h5 : Real.sin (Real.pi / 6) = 1 / 2 := by
    rw [sin_pi_div_six]
  rw [h2, h3, h4, h5]
  have h9 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num)]
    all_goals norm_num
  field_simp [h9]
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), 
            Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), 
            Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num : (0 : ℝ) < 6), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num : (0 : ℝ) ≤ (6 : ℝ)), 
            sq_nonneg (Real.sqrt 2 - Real.sqrt 6 / 2)
          ]