import Mathlib

theorem algebra_164063 (a b : ℝ) (ha : a = Real.sin (Real.pi / 12)) (hb : b = Real.cos (Real.pi / 12)) :
    a = (Real.sqrt 6 - Real.sqrt 2) / 4 ∧ b = (Real.sqrt 6 + Real.sqrt 2) / 4 := by
  have ha1 : a = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
    rw [ha]
    have h1 : Real.sin (Real.pi / 12) = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
      have h2 : Real.sin (Real.pi / 12) = Real.sin (Real.pi / 4 - Real.pi / 6) := by
        ring_nf
      rw [h2]
      rw [Real.sin_sub]
      have h3 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        exact Real.sin_pi_div_four
      have h4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
        exact Real.cos_pi_div_four
      have h5 : Real.sin (Real.pi / 6) = 1 / 2 := by 
        exact Real.sin_pi_div_six
      have h6 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
        exact Real.cos_pi_div_six
      rw [h3, h4, h5, h6]
      have h7 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
        rw [← Real.sqrt_mul (by norm_num)]
        all_goals norm_num
      field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num : (6 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num : (6 : ℝ) ≥ 0), h7]
    exact h1
  have hb1 : b = (Real.sqrt 6 + Real.sqrt 2) / 4 := by 
    rw [hb]
    have h1 : Real.cos (Real.pi / 12) = (Real.sqrt 6 + Real.sqrt 2) / 4 := by
      have h2 : Real.cos (Real.pi / 12) = Real.cos (Real.pi / 4 - Real.pi / 6) := by
        ring_nf
      rw [h2]
      rw [Real.cos_sub]
      have h3 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := by 
        exact Real.cos_pi_div_four
      have h4 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := by 
        exact Real.cos_pi_div_six
      have h5 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by 
        exact Real.sin_pi_div_four
      have h6 : Real.sin (Real.pi / 6) = 1 / 2 := by
        exact Real.sin_pi_div_six
      rw [h3, h4, h5, h6]
      have h7 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
        rw [← Real.sqrt_mul (by norm_num)]
        all_goals norm_num
      field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num : (6 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num : (6 : ℝ) ≥ 0), h7]
    exact h1
  constructor
  · exact ha1
  · exact hb1