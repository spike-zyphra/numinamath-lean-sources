import Mathlib

theorem algebra_189152 : (Real.cos (73 * Real.pi / 180))^2 + (Real.cos (47 * Real.pi / 180))^2 +
    Real.cos (73 * Real.pi / 180) * Real.cos (47 * Real.pi / 180) = 3 / 4 := by
  have h3 : Real.cos (47 * Real.pi / 180) = -1 / 2 * Real.cos (73 * Real.pi / 180) + Real.sqrt 3 / 2 * Real.sin (73 * Real.pi / 180) := by
    have h2 : Real.cos (47 * Real.pi / 180) = Real.cos ( (2 * Real.pi / 3 ) - (73 * Real.pi / 180) ) := by
      ring_nf
    rw [h2]
    have h4 : Real.cos ((2 * Real.pi / 3) - (73 * Real.pi / 180)) =
      Real.cos (2 * Real.pi / 3) * Real.cos (73 * Real.pi / 180) + Real.sin (2 * Real.pi / 3) * Real.sin (73 * Real.pi / 180) := by
      rw [Real.cos_sub]
    rw [h4]
    have h5 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
      have h6 : Real.cos (2 * Real.pi / 3) = Real.cos (Real.pi - Real.pi / 3) := by 
        ring_nf
      rw [h6]
      rw [Real.cos_pi_sub]
      norm_num
    have h7 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
      have h8 : Real.sin (2 * Real.pi / 3) = Real.sin (Real.pi - Real.pi / 3) := by 
        ring_nf
      rw [h8]
      rw [Real.sin_pi_sub]
      have h9 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
      linarith
    rw [h5, h7]
    all_goals ring_nf
  rw [h3]
  have h6 : (Real.cos (73 * Real.pi / 180)) ^ 2 + ( -1 / 2 * Real.cos (73 * Real.pi / 180) + Real.sqrt 3 / 2 * Real.sin (73 * Real.pi / 180) ) ^ 2 +
          (Real.cos (73 * Real.pi / 180)) * ( -1 / 2 * Real.cos (73 * Real.pi / 180) + Real.sqrt 3 / 2 * Real.sin (73 * Real.pi / 180) ) =
          3 / 4 := by
    nlinarith [ Real.sin_sq_add_cos_sq (73 * Real.pi / 180), Real.sin_sq_add_cos_sq (47 * Real.pi / 180), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
      sq_nonneg (Real.cos (73 * Real.pi / 180) - Real.sin (73 * Real.pi / 180)), sq_nonneg (Real.cos (73 * Real.pi / 180) + Real.sin (73 * Real.pi / 180))
    ]
  linarith