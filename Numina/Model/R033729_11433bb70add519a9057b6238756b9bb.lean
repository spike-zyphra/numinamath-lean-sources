import Mathlib

theorem algebra_258487 : Real.sin (Real.pi / 8) ^ 4 + Real.sin (3 * Real.pi / 8) ^ 4 +
    Real.sin (5 * Real.pi / 8) ^ 4 + Real.sin (7 * Real.pi / 8) ^ 4 = 3 / 2 := by
  have h1 : Real.sin (Real.pi / 8) ^ 2 = (1 - Real.cos (Real.pi / 4)) / 2 := by
    have h2 : Real.sin (Real.pi / 8) ^ 2 = (1 - Real.cos (2 * (Real.pi / 8)) ) / 2 := by
      rw [Real.sin_sq_eq_half_sub]
      ring
    rw [h2]
    ring_nf
  have h2 : Real.sin (3 * Real.pi / 8) ^ 2 = (1 - Real.cos (3 * Real.pi / 4)) / 2 := by
    have h3 : Real.sin (3 * Real.pi / 8) ^ 2 = (1 - Real.cos (2 * (3 * Real.pi / 8)) ) / 2 := by
      rw [Real.sin_sq_eq_half_sub]
      ring
    rw [h3]
    ring_nf
  have h3 : Real.sin (5 * Real.pi / 8) ^ 2 = (1 - Real.cos (5 * Real.pi / 4)) / 2 := by
    have h4 : Real.sin (5 * Real.pi / 8) ^ 2 = (1 - Real.cos (2 * (5 * Real.pi / 8)) ) / 2 := by
      rw [Real.sin_sq_eq_half_sub]
      ring
    rw [h4]
    ring_nf
  have h4 : Real.sin (7 * Real.pi / 8) ^ 2 = (1 - Real.cos (7 * Real.pi / 4)) / 2 := by
    have h5 : Real.sin (7 * Real.pi / 8) ^ 2 = (1 - Real.cos (2 * (7 * Real.pi / 8)) ) / 2 := by
      rw [Real.sin_sq_eq_half_sub]
      ring
    rw [h5]
    ring_nf
  have h5 : Real.cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
    have h1 : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by
      ring
    rw [h1]
    rw [Real.cos_pi_sub]
    have h2 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    linarith [h2]
  have h6 : Real.cos (5 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
    have h1 : 5 * Real.pi / 4 = Real.pi + Real.pi / 4 := by
      ring
    rw [h1]
    have h2 : Real.cos (Real.pi + Real.pi / 4) = -Real.cos (Real.pi / 4) := by 
      rw [Real.cos_add, Real.cos_pi, Real.sin_pi]
      all_goals ring
    have h3 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    rw [h2, h3]
    all_goals ring
  have h7 : Real.cos (7 * Real.pi / 4) = Real.sqrt 2 / 2 := by
    have h1 : 7 * Real.pi / 4 = 2 * Real.pi - Real.pi / 4 := by
      ring
    rw [h1]
    have h2 : Real.cos (2 * Real.pi - Real.pi / 4) = Real.cos (Real.pi / 4) := by 
      rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
      all_goals ring
    have h3 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    rw [h2, h3]
  have h8 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have h9 : Real.sin (Real.pi / 8) ^ 4 = ((1 - Real.sqrt 2 / 2) / 2) ^ 2 := by
    calc 
      Real.sin (Real.pi / 8) ^ 4 = (Real.sin (Real.pi / 8) ^ 2) ^ 2 := by ring
      _ = ((1 - Real.cos (Real.pi / 4)) / 2) ^ 2 := by rw [h1]
      _ = ((1 - Real.sqrt 2 / 2) / 2) ^ 2 := by 
        rw [h8]
  have h10 : Real.sin (3 * Real.pi / 8) ^ 4 = ((1 + Real.sqrt 2 / 2) / 2) ^ 2 := by
    calc 
      Real.sin (3 * Real.pi / 8) ^ 4 = (Real.sin (3 * Real.pi / 8) ^ 2) ^ 2 := by ring
      _ = ((1 - Real.cos (3 * Real.pi / 4)) / 2) ^ 2 := by rw [h2]
      _ = ((1 - (-Real.sqrt 2 / 2)) / 2) ^ 2 := by 
        rw [h5]
      _ = ((1 + Real.sqrt 2 / 2) / 2) ^ 2 := by ring
  have h11 : Real.sin (5 * Real.pi / 8) ^ 4 = ((1 + Real.sqrt 2 / 2) / 2) ^ 2 := by
    calc 
      Real.sin (5 * Real.pi / 8) ^ 4 = (Real.sin (5 * Real.pi / 8) ^ 2) ^ 2 := by ring
      _ = ((1 - Real.cos (5 * Real.pi / 4)) / 2) ^ 2 := by rw [h3]
      _ = ((1 - (-Real.sqrt 2 / 2)) / 2) ^ 2 := by 
        rw [h6]
      _ = ((1 + Real.sqrt 2 / 2) / 2) ^ 2 := by ring
  have h12 : Real.sin (7 * Real.pi / 8) ^ 4 = ((1 - Real.sqrt 2 / 2) / 2) ^ 2 := by
    calc 
      Real.sin (7 * Real.pi / 8) ^ 4 = (Real.sin (7 * Real.pi / 8) ^ 2) ^ 2 := by ring
      _ = ((1 - Real.cos (7 * Real.pi / 4)) / 2) ^ 2 := by rw [h4]
      _ = ((1 - Real.sqrt 2 / 2) / 2) ^ 2 := by 
        rw [h7]
  calc
    Real.sin (Real.pi / 8) ^ 4 + Real.sin (3 * Real.pi / 8) ^ 4 + 
      Real.sin (5 * Real.pi / 8) ^ 4 + Real.sin (7 * Real.pi / 8) ^ 4 
    = ((1 - Real.sqrt 2 / 2) / 2) ^ 2 + ((1 + Real.sqrt 2 / 2) / 2) ^ 2 + ((1 + Real.sqrt 2 / 2) / 2) ^ 2 + ((1 - Real.sqrt 2 / 2) / 2) ^ 2 := by
      rw [h9, h10, h11, h12]
    _ = 3 / 2 := by 
      ring_nf
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]