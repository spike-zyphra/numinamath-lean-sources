import Mathlib

theorem algebra_164541 : (Real.sin (22 * Real.pi / 180) * Real.cos (8 * Real.pi / 180) +
    Real.cos (158 * Real.pi / 180) * Real.cos (98 * Real.pi / 180)) /
    (Real.sin (23 * Real.pi / 180) * Real.cos (7 * Real.pi / 180) +
    Real.cos (157 * Real.pi / 180) * Real.cos (97 * Real.pi / 180)) = 1 := by

  have h1 : Real.cos (158 * Real.pi / 180) = - Real.cos (22 * Real.pi / 180) := by
    have h1 : 158 * Real.pi / 180 = Real.pi - 22 * Real.pi / 180 := by
      linarith [Real.pi_pos]
    rw [h1]
    rw [Real.cos_pi_sub]

  have h2 : Real.cos (98 * Real.pi / 180) = - Real.sin (8 * Real.pi / 180) := by
    have h2 : 98 * Real.pi / 180 = Real.pi / 2 + 8 * Real.pi / 180 := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [Real.cos_add]
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring

  have h3 : Real.cos (157 * Real.pi / 180) = - Real.cos (23 * Real.pi / 180) := by
    have h3 : 157 * Real.pi / 180 = Real.pi - 23 * Real.pi / 180 := by
      linarith [Real.pi_pos]
    rw [h3]
    rw [Real.cos_pi_sub]

  have h4 : Real.cos (97 * Real.pi / 180) = - Real.sin (7 * Real.pi / 180) := by
    have h4 : 97 * Real.pi / 180 = Real.pi / 2 + 7 * Real.pi / 180 := by
      linarith [Real.pi_pos]
    rw [h4]
    rw [Real.cos_add]
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring

  have h5 : Real.sin (22 * Real.pi / 180) * Real.cos (8 * Real.pi / 180) +
    Real.cos (158 * Real.pi / 180) * Real.cos (98 * Real.pi / 180) = 1 / 2 := by
    rw [h1, h2]
    have h : Real.sin (22 * Real.pi / 180) * Real.cos (8 * Real.pi / 180) + (- Real.cos (22 * Real.pi / 180)) * (- Real.sin (8 * Real.pi / 180)) = Real.sin (22 * Real.pi / 180 + 8 * Real.pi / 180) := by
      rw [Real.sin_add]
      ring
    rw [h]
    have h228 : 22 * Real.pi / 180 + 8 * Real.pi / 180 = Real.pi / 6 := by
      linarith [Real.pi_pos]
    rw [h228]
    rw [Real.sin_pi_div_six]

  have h6 : Real.sin (23 * Real.pi / 180) * Real.cos (7 * Real.pi / 180) +
    Real.cos (157 * Real.pi / 180) * Real.cos (97 * Real.pi / 180) = 1 / 2 := by
    rw [h3, h4]
    have h : Real.sin (23 * Real.pi / 180) * Real.cos (7 * Real.pi / 180) + (- Real.cos (23 * Real.pi / 180)) * (- Real.sin (7 * Real.pi / 180)) = Real.sin (23 * Real.pi / 180 + 7 * Real.pi / 180) := by
      rw [Real.sin_add]
      ring
    rw [h]
    have h228 : 23 * Real.pi / 180 + 7 * Real.pi / 180 = Real.pi / 6 := by
      linarith [Real.pi_pos]
    rw [h228]
    rw [Real.sin_pi_div_six]

  rw [h5, h6]
  norm_num