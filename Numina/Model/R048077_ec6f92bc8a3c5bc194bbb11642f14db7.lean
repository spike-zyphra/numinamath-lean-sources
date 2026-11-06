import Mathlib

theorem algebra_246565 : Real.sin (Real.pi / 8) ^ 4 + Real.cos (3 * Real.pi / 8) ^ 4 = 3 / 4 - Real.sqrt 2 / 2 := by
  have h1 : 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 := by
    ring
  have h2 : Real.cos (3 * Real.pi / 8) = Real.sin (Real.pi / 8) := by
    rw [h1]
    rw [Real.cos_pi_div_two_sub]
  rw [h2]
  have h3 : Real.sin (Real.pi / 8) ^ 4 + Real.sin (Real.pi / 8) ^ 4 = 3 / 4 - Real.sqrt 2 / 2 := by
    have h4 : Real.sin (Real.pi / 8) ^ 2 = (1 - Real.sqrt 2 / 2) / 2 := by
      have h5 : Real.sin (Real.pi / 8) ^ 2 = (1 - Real.cos (Real.pi / 4)) / 2 := by
        have h6 : Real.sin (Real.pi / 8) ^ 2 = (1 - Real.cos (2 * (Real.pi / 8)) ) / 2 := by 
          rw [Real.sin_sq_eq_half_sub]
          ring
        rw [h6]
        ring
      have h7 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      rw [h7] at h5
      linarith
    have h8 : Real.sin (Real.pi / 8) ^ 4 = ((1 - Real.sqrt 2 / 2) / 2) ^ 2 := by
      calc
        Real.sin (Real.pi / 8) ^ 4 = (Real.sin (Real.pi / 8) ^ 2) ^ 2 := by ring
        _ = ((1 - Real.sqrt 2 / 2) / 2) ^ 2 := by rw [h4]
    nlinarith [h8, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by linarith : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith : (2 : ℝ) ≥ 0)]
  linarith [h3]