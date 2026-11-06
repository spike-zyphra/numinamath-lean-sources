import Mathlib

theorem algebra_163706 (α : ℝ) :
    Real.sin (5 / 4 * Real.pi - 2 * α) ^ 2 - Real.sin (5 / 4 * Real.pi + 2 * α) ^ 2 =
    -Real.sin (4 * α) := by 
  have h1 : Real.sin (5 / 4 * Real.pi - 2 * α) ^ 2 = (1 - Real.cos (2 * (5 / 4 * Real.pi - 2 * α)) ) / 2 := by
    rw [Real.sin_sq_eq_half_sub]
    <;> ring
  have h2 : Real.sin (5 / 4 * Real.pi + 2 * α) ^ 2 = (1 - Real.cos (2 * (5 / 4 * Real.pi + 2 * α)) ) / 2 := by
    rw [Real.sin_sq_eq_half_sub]
    <;> ring
  rw [h1, h2]

  have h3 : 2 * (5 / 4 * Real.pi - 2 * α) = 5 / 2 * Real.pi - 4 * α := by ring
  have h4 : 2 * (5 / 4 * Real.pi + 2 * α) = 5 / 2 * Real.pi + 4 * α := by ring
  rw [h3, h4]

  have h5 : Real.cos (5 / 2 * Real.pi + 4 * α) = - Real.sin (4 * α) := by
    have h6 : Real.cos (5 / 2 * Real.pi + 4 * α) = Real.cos (Real.pi / 2 + 4 * α + 2 * Real.pi) := by 
      ring_nf
    have h7 : Real.cos (Real.pi / 2 + 4 * α + 2 * Real.pi) = Real.cos (Real.pi / 2 + 4 * α) := by
      have h10 : Real.cos (Real.pi / 2 + 4 * α + 2 * Real.pi) = 
          Real.cos (Real.pi / 2 + 4 * α) * Real.cos (2 * Real.pi) - Real.sin (Real.pi / 2 + 4 * α) * Real.sin (2 * Real.pi) := by
        rw [show Real.pi / 2 + 4 * α + 2 * Real.pi = (Real.pi / 2 + 4 * α) + (2 * Real.pi) by ring]
        rw [Real.cos_add]
      rw [h10]
      have h11 : Real.cos (2 * Real.pi) = (1 : ℝ) := Real.cos_two_pi
      have h12 : Real.sin (2 * Real.pi) = (0 : ℝ) := Real.sin_two_pi
      simp [h11, h12]
      all_goals ring_nf <;> norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]
    have h8 : Real.cos (Real.pi / 2 + 4 * α) = - Real.sin (4 * α) := by 
      rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring
    rw [h6, h7, h8]

  have h9 : Real.cos (5 / 2 * Real.pi - 4 * α) = Real.sin (4 * α) := by 
    have h8 : Real.cos (5 / 2 * Real.pi - 4 * α) = Real.cos (Real.pi / 2 - 4 * α + 2 * Real.pi) := by 
      ring_nf
    rw [h8]
    have h9 : Real.cos (Real.pi / 2 - 4 * α + 2 * Real.pi) = Real.cos (Real.pi / 2 - 4 * α) := by
      have h10 : Real.cos (Real.pi / 2 - 4 * α + 2 * Real.pi) =
          Real.cos (Real.pi / 2 - 4 * α) * Real.cos (2 * Real.pi) - Real.sin (Real.pi / 2 - 4 * α) * Real.sin (2 * Real.pi) := by
        rw [show Real.pi / 2 - 4 * α + 2 * Real.pi = (Real.pi / 2 - 4 * α) + (2 * Real.pi) by ring]
        rw [Real.cos_add]
      rw [h10]
      have h11 : Real.cos (2 * Real.pi) = (1 : ℝ) := Real.cos_two_pi
      have h12 : Real.sin (2 * Real.pi) = (0 : ℝ) := Real.sin_two_pi
      simp [h11, h12]
      all_goals ring_nf <;> norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]
    rw [h9]
    have h10 : Real.cos (Real.pi / 2 - 4 * α) = Real.sin (4 * α) := by 
      rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring
    exact h10

  linarith [h5, h9]