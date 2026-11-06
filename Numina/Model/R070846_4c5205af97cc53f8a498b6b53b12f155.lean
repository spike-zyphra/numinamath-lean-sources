import Mathlib

theorem algebra_304318 : Real.sin (Real.pi / 8) ^ 4 + Real.cos (3 * Real.pi / 8) ^ 4 +
    Real.sin (5 * Real.pi / 8) ^ 4 + Real.cos (7 * Real.pi / 8) ^ 4 = 3 / 2 := by 
  have h1 : Real.sin (5 * Real.pi / 8) = Real.sin (3 * Real.pi / 8) := by
    have h1 : 5 * Real.pi / 8 = Real.pi - 3 * Real.pi / 8 := by 
      linarith [Real.pi_pos]
    rw [h1]
    rw [Real.sin_pi_sub]
  have h2 : Real.cos (7 * Real.pi / 8) = - Real.cos (Real.pi / 8) := by
    have h2 : 7 * Real.pi / 8 = Real.pi - Real.pi / 8 := by 
      linarith [Real.pi_pos]
    rw [h2]
    rw [Real.cos_pi_sub]
  have h3 : Real.sin (5 * Real.pi / 8) ^ 4 = Real.sin (3 * Real.pi / 8) ^ 4 := by 
    rw [h1]
  have h4 : Real.cos (7 * Real.pi / 8) ^ 4 = Real.cos (Real.pi / 8) ^ 4 := by 
    rw [h2]
    ring
  rw [h3, h4]
  have h5 : Real.sin (Real.pi / 8) ^ 4 + Real.cos (Real.pi / 8) ^ 4 = 3 / 4 := by 
    have h51 : Real.sin (Real.pi / 8) ^ 2 + Real.cos (Real.pi / 8) ^ 2 = 1 := Real.sin_sq_add_cos_sq (Real.pi / 8)
    have h52 : Real.sin (2 * (Real.pi / 8)) = 2 * Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8) := by 
      rw [Real.sin_two_mul]
    have h53 : Real.sin (2 * (Real.pi / 8)) ^ 2 = 1 / 2 := by 
      have h531 : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
      rw [h531]
      have h532 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
      rw [h532]
      have h533 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by 
        calc 
          (Real.sqrt 2 / 2: ℝ) ^ 2 = (Real.sqrt 2) ^ 2 / 4 := by ring 
          _ = (2: ℝ) / 4 := by rw [Real.sq_sqrt]; linarith 
          _ = (1: ℝ) / 2 := by norm_num
      linarith
    have h54 : Real.sin (Real.pi / 8) ^ 4 + Real.cos (Real.pi / 8) ^ 4 = (Real.sin (Real.pi / 8) ^ 2 + Real.cos (Real.pi / 8) ^ 2) ^ 2 - 2 * (Real.sin (2 * (Real.pi / 8)) ^ 2 / 4) := by 
      have h1 : Real.sin (2 * (Real.pi / 8)) = 2 * Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8) := by 
        rw [Real.sin_two_mul]
      have h2 : Real.sin (2 * (Real.pi / 8)) ^ 2 = (2 * Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8)) ^ 2 := by 
        rw [h1]
      have h3 : Real.sin (Real.pi / 8) ^ 4 + Real.cos (Real.pi / 8) ^ 4 = (Real.sin (Real.pi / 8) ^ 2 + Real.cos (Real.pi / 8) ^ 2) ^ 2 - 2 * (Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8)) ^ 2 := by 
        ring
      have h4 : (Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8)) ^ 2 = Real.sin (2 * (Real.pi / 8)) ^ 2 / 4 := by 
        nlinarith [h1]
      linarith [h3, h4]
    rw [h51, h53] at h54
    nlinarith
  have h6 : Real.sin (3 * Real.pi / 8) ^ 4 + Real.cos (3 * Real.pi / 8) ^ 4 = 3 / 4 := by 
    have h61 : Real.sin (3 * Real.pi / 8) ^ 2 + Real.cos (3 * Real.pi / 8) ^ 2 = 1 := Real.sin_sq_add_cos_sq (3 * Real.pi / 8)
    have h62 : Real.sin (2 * (3 * Real.pi / 8)) = 2 * Real.sin (3 * Real.pi / 8) * Real.cos (3 * Real.pi / 8) := by 
      rw [Real.sin_two_mul]
    have h63 : Real.sin (2 * (3 * Real.pi / 8)) ^ 2 = 1 / 2 := by 
      have h631 : 2 * (3 * Real.pi / 8) = 3 * Real.pi / 4 := by ring
      rw [h631]
      have h632 : Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by 
        have h1 : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
        rw [h1]
        rw [Real.sin_pi_sub]
        have h2 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
        linarith
      rw [h632]
      have h633 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by 
        calc 
          (Real.sqrt 2 / 2: ℝ) ^ 2 = (Real.sqrt 2) ^ 2 / 4 := by ring 
          _ = (2: ℝ) / 4 := by rw [Real.sq_sqrt]; linarith 
          _ = (1: ℝ) / 2 := by norm_num
      linarith
    have h64 : Real.sin (3 * Real.pi / 8) ^ 4 + Real.cos (3 * Real.pi / 8) ^ 4 = (Real.sin (3 * Real.pi / 8) ^ 2 + Real.cos (3 * Real.pi / 8) ^ 2) ^ 2 - 2 * (Real.sin (2 * (3 * Real.pi / 8)) ^ 2 / 4) := by 
      have h1 : Real.sin (2 * (3 * Real.pi / 8)) = 2 * Real.sin (3 * Real.pi / 8) * Real.cos (3 * Real.pi / 8) := by 
        rw [Real.sin_two_mul]
      have h2 : Real.sin (2 * (3 * Real.pi / 8)) ^ 2 = (2 * Real.sin (3 * Real.pi / 8) * Real.cos (3 * Real.pi / 8)) ^ 2 := by 
        rw [h1]
      have h3 : Real.sin (3 * Real.pi / 8) ^ 4 + Real.cos (3 * Real.pi / 8) ^ 4 = (Real.sin (3 * Real.pi / 8) ^ 2 + Real.cos (3 * Real.pi / 8) ^ 2) ^ 2 - 2 * (Real.sin (3 * Real.pi / 8) * Real.cos (3 * Real.pi / 8)) ^ 2 := by 
        ring
      have h4 : (Real.sin (3 * Real.pi / 8) * Real.cos (3 * Real.pi / 8)) ^ 2 = Real.sin (2 * (3 * Real.pi / 8)) ^ 2 / 4 := by 
        nlinarith [h1]
      linarith [h3, h4]
    rw [h61, h63] at h64
    nlinarith
  linarith [h5, h6]