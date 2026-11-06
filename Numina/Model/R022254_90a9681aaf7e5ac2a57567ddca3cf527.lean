import Mathlib

theorem algebra_178547 (α : ℝ) :
    2 * Real.sin (3 * Real.pi - 2 * α) ^ 2 * Real.cos (5 * Real.pi + 2 * α) ^ 2 =
    1 / 4 - 1 / 4 * Real.sin ((5 * Real.pi / 2) - 8 * α) := by
  have h1 : Real.sin (3 * Real.pi - 2 * α) = Real.sin (2 * α) := by
    have h2 : 3 * Real.pi - 2 * α = Real.pi - (2 * α) + 2 * Real.pi := by
      linarith [Real.pi_pos]
    rw [h2]
    have h3 : Real.sin (Real.pi - (2 * α) + 2 * Real.pi) = Real.sin (Real.pi - (2 * α)) := by
      rw [show Real.pi - (2 * α) + 2 * Real.pi = (Real.pi - (2 * α)) + 2 * Real.pi by ring]
      rw [Real.sin_add_two_pi]
    have h4 : Real.sin (Real.pi - (2 * α)) = Real.sin (2 * α) := by
      rw [show Real.pi - (2 * α) = Real.pi - (2 * α) by rfl]
      rw [Real.sin_pi_sub]
    rw [h3, h4]
  have h2 : Real.cos (5 * Real.pi + 2 * α) = - Real.cos (2 * α) := by
    have h3 : 5 * Real.pi + 2 * α = Real.pi + 2 * α + 4 * Real.pi := by
      linarith [Real.pi_pos]
    rw [h3]
    have h4 : Real.cos (Real.pi + 2 * α + 4 * Real.pi) = Real.cos (Real.pi + 2 * α) := by
      have h6 : Real.pi + 2 * α + 4 * Real.pi = (Real.pi + 2 * α) + 2 * (2 * Real.pi) := by 
        ring
      rw [h6]
      have h7 : Real.cos ((Real.pi + 2 * α) + 2 * (2 * Real.pi)) = Real.cos (Real.pi + 2 * α) := by
        have h8 : Real.cos ((Real.pi + 2 * α) + 2 * (2 * Real.pi)) = Real.cos (Real.pi + 2 * α) := by 
          have h9 : (Real.pi + 2 * α) + 2 * (2 * Real.pi) = (Real.pi + 2 * α) + (2 : ℕ) * (2 * Real.pi) := by 
            ring_nf
          rw [h9]
          rw [Real.cos_add_nat_mul_two_pi]
        linarith [h8]
      linarith [h7]
    have h7 : Real.cos (Real.pi + 2 * α) = - Real.cos (2 * α) := by
      rw [Real.cos_add]
      simp [Real.cos_pi, Real.sin_pi]
      all_goals ring
    rw [h4, h7]
  have h3 : Real.sin ((5 * Real.pi / 2) - 8 * α) = Real.cos (8 * α) := by
    have h4 : (5 * Real.pi / 2) - 8 * α = Real.pi / 2 - 8 * α + 2 * Real.pi := by
      linarith [Real.pi_pos]
    rw [h4]
    have h5 : Real.sin (Real.pi / 2 - 8 * α + 2 * Real.pi) = Real.sin (Real.pi / 2 - 8 * α) := by
      rw [show Real.pi / 2 - 8 * α + 2 * Real.pi = (Real.pi / 2 - 8 * α) + 2 * Real.pi by ring]
      rw [Real.sin_add_two_pi]
    have h6 : Real.sin (Real.pi / 2 - 8 * α) = Real.cos (8 * α) := by
      rw [Real.sin_pi_div_two_sub]
    rw [h5, h6]

  rw [h1, h2, h3]
  have h4 : 8 * Real.sin (2 * α) ^ 2 * Real.cos (2 * α) ^ 2 = 1 - Real.cos (8 * α) := by
    have h5 : Real.cos (8 * α) = 1 - 2 * (Real.sin (4 * α) ^ 2) := by
      have h6 : 8 * α = 2 * (4 * α) := by ring
      rw [h6]
      have h7 : Real.cos (2 * (4 * α)) = 1 - 2 * (Real.sin (4 * α) ^ 2) := by
        rw [Real.cos_two_mul, Real.sin_sq]
        all_goals ring
      linarith
    have h6 : Real.sin (4 * α) = 2 * Real.sin (2 * α) * Real.cos (2 * α) := by
      have h7 : 4 * α = 2 * (2 * α) := by ring
      rw [h7]
      rw [Real.sin_two_mul]
    rw [h6] at h5
    nlinarith
  have h5 : 2 * Real.sin (2 * α) ^ 2 * Real.cos (2 * α) ^ 2 = 1 / 4 * (1 - Real.cos (8 * α)) := by
    nlinarith [h4]
  have h6 : 2 * Real.sin (2 * α) ^ 2 * Real.cos (2 * α) ^ 2 = 2 * Real.sin (2 * α) ^ 2 * Real.cos (2 * α) ^ 2 := by 
    rfl
  nlinarith