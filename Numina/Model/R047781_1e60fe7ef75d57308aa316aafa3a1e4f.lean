import Mathlib

theorem algebra_138691 : 2 * (Real.cos (5 * Real.pi / 16))^6 + 2 * (Real.sin (11 * Real.pi / 16))^6 + 3 * Real.sqrt 2 / 8 = 5 / 4 := by
  have h1 : Real.sin (11 * Real.pi / 16) = Real.sin (5 * Real.pi / 16) := by
    have h2 : 11 * Real.pi / 16 = Real.pi - (5 * Real.pi / 16) := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [Real.sin_pi_sub]
  rw [h1]
  have h2 : 2 * (Real.cos (5 * Real.pi / 16)) ^ 6 + 2 * (Real.sin (5 * Real.pi / 16)) ^ 6 = 2 - 6 * (Real.cos (5 * Real.pi / 16) ^ 2 * Real.sin (5 * Real.pi / 16) ^ 2) := by
    have h3 : (Real.cos (5 * Real.pi / 16)) ^ 6 + (Real.sin (5 * Real.pi / 16)) ^ 6 = 1 - 3 * (Real.cos (5 * Real.pi / 16) ^ 2 * Real.sin (5 * Real.pi / 16) ^ 2) := by
      have h4 : (Real.cos (5 * Real.pi / 16)) ^ 2 + (Real.sin (5 * Real.pi / 16)) ^ 2 = 1 := by
        exact Real.cos_sq_add_sin_sq (5 * Real.pi / 16)
      have h5 : (Real.cos (5 * Real.pi / 16)) ^ 6 + (Real.sin (5 * Real.pi / 16)) ^ 6 = ((Real.cos (5 * Real.pi / 16)) ^ 2) ^ 3 + ((Real.sin (5 * Real.pi / 16)) ^ 2) ^ 3 := by ring
      rw [h5]
      have h6 : ((Real.cos (5 * Real.pi / 16)) ^ 2) ^ 3 + ((Real.sin (5 * Real.pi / 16)) ^ 2) ^ 3 = ((Real.cos (5 * Real.pi / 16)) ^ 2 + (Real.sin (5 * Real.pi / 16)) ^ 2) ^ 3 - 3 * ((Real.cos (5 * Real.pi / 16)) ^ 2 * (Real.sin (5 * Real.pi / 16)) ^ 2) * ((Real.cos (5 * Real.pi / 16)) ^ 2 + (Real.sin (5 * Real.pi / 16)) ^ 2) := by ring
      rw [h6, h4]
      all_goals nlinarith
    linarith [h3]
  have h3 : Real.cos (5 * Real.pi / 16) ^ 2 * Real.sin (5 * Real.pi / 16) ^ 2 = (2 + Real.sqrt 2) / 16 := by
    have h4 : Real.cos (5 * Real.pi / 16) ^ 2 * Real.sin (5 * Real.pi / 16) ^ 2 = (Real.sin (2 * (5 * Real.pi / 16)) ) ^ 2 / 4 := by
      have h5 : Real.sin (2 * (5 * Real.pi / 16)) = 2 * Real.sin (5 * Real.pi / 16) * Real.cos (5 * Real.pi / 16) := by
        rw [Real.sin_two_mul]
      have h6 : (Real.sin (2 * (5 * Real.pi / 16)) ) ^ 2 = 4 * (Real.sin (5 * Real.pi / 16)) ^ 2 * (Real.cos (5 * Real.pi / 16)) ^ 2 := by
        rw [h5]
        ring
      nlinarith [h6]
    have h5 : Real.sin (2 * (5 * Real.pi / 16)) ^ 2 = (2 + Real.sqrt 2) / 4 := by
      have h7 : 2 * (5 * Real.pi / 16) = 5 * Real.pi / 8 := by ring
      rw [h7]
      have h8 : Real.sin (5 * Real.pi / 8) ^ 2 = Real.sin (3 * Real.pi / 8) ^ 2 := by
        have h9 : 5 * Real.pi / 8 = Real.pi - (3 * Real.pi / 8) := by linarith [Real.pi_pos]
        rw [h9]
        rw [Real.sin_pi_sub]
      rw [h8]
      have h10 : Real.sin (3 * Real.pi / 8) ^ 2 = (1 - Real.cos (3 * Real.pi / 4)) / 2 := by
        have h11 : Real.sin (3 * Real.pi / 8) ^ 2 = (1 - Real.cos (2 * (3 * Real.pi / 8)) ) / 2 := by
          rw [Real.sin_sq_eq_half_sub]
          ring_nf
        rw [h11]
        ring_nf
      rw [h10]
      have h11 : Real.cos (3 * Real.pi / 4) = - Real.sqrt 2 / 2 := by
        have h12 : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by linarith [Real.pi_pos]
        rw [h12]
        rw [Real.cos_pi_sub]
        have h13 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
        linarith [h13]
      rw [h11]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h4, h5]
    all_goals nlinarith
  rw [h2, h3]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]