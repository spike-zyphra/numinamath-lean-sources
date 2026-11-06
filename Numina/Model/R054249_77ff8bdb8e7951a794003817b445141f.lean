import Mathlib

theorem algebra_185823 (α : ℝ) :
    Real.sin ((9 / 8) * Real.pi + α) ^ 2 - Real.sin ((17 / 8) * Real.pi - α) ^ 2 =
    (1 / Real.sqrt 2) * Real.sin (2 * α) := by
  have h1 : Real.sin ((9 / 8) * Real.pi + α) ^ 2 = (1 - Real.cos (2 * ((9 / 8) * Real.pi + α)) ) / 2 := by
    rw [Real.sin_sq_eq_half_sub]
    ring
  have h2 : Real.sin ((17 / 8) * Real.pi - α) ^ 2 = (1 - Real.cos (2 * ((17 / 8) * Real.pi - α)) ) / 2 := by
    rw [Real.sin_sq_eq_half_sub]
    ring
  rw [h1, h2]
  have h3 : 2 * ((9 / 8) * Real.pi + α) = (9 / 4) * Real.pi + 2 * α := by ring
  have h4 : 2 * ((17 / 8) * Real.pi - α) = (17 / 4) * Real.pi - 2 * α := by ring
  rw [h3, h4]
  have h5 : Real.cos ((9 / 4) * Real.pi + 2 * α) = Real.cos (Real.pi / 4 + 2 * α) := by
    have h6 : (9 / 4) * Real.pi + 2 * α = Real.pi / 4 + 2 * α + 2 * Real.pi := by
      nlinarith [Real.pi_pos]
    rw [h6]
    have h7 : Real.cos (Real.pi / 4 + 2 * α + 2 * Real.pi) = Real.cos (Real.pi / 4 + 2 * α) := by
      rw [Real.cos_add_two_pi]
    linarith [h7]
  have h7 : Real.cos ((17 / 4) * Real.pi - 2 * α) = Real.cos (Real.pi / 4 - 2 * α) := by
    have h8 : (17 / 4) * Real.pi - 2 * α = Real.pi / 4 - 2 * α + 4 * Real.pi := by
      nlinarith [Real.pi_pos]
    rw [h8]
    have h9 : Real.cos (Real.pi / 4 - 2 * α + 4 * Real.pi) = Real.cos (Real.pi / 4 - 2 * α) := by
      have h10 : Real.cos (Real.pi / 4 - 2 * α + 4 * Real.pi) = Real.cos ( (Real.pi / 4 - 2 * α + 2 * Real.pi) + 2 * Real.pi ) := by ring_nf
      rw [h10]
      have h11 : Real.cos ( (Real.pi / 4 - 2 * α + 2 * Real.pi) + 2 * Real.pi ) = Real.cos (Real.pi / 4 - 2 * α + 2 * Real.pi) := by
        rw [Real.cos_add_two_pi]
      rw [h11]
      have h12 : Real.cos (Real.pi / 4 - 2 * α + 2 * Real.pi) = Real.cos (Real.pi / 4 - 2 * α) := by
        rw [Real.cos_add_two_pi]
      rw [h12]
    linarith [h9]
  rw [h5, h7]
  have h8 : Real.cos (Real.pi / 4 + 2 * α) = Real.cos (Real.pi / 4) * Real.cos (2 * α) - Real.sin (Real.pi / 4) * Real.sin (2 * α) := by
    rw [Real.cos_add]
  have h9 : Real.cos (Real.pi / 4 - 2 * α) = Real.cos (Real.pi / 4) * Real.cos (2 * α) + Real.sin (Real.pi / 4) * Real.sin (2 * α) := by
    rw [Real.cos_sub]
  rw [h8, h9]
  have h10 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [Real.cos_pi_div_four]
  have h11 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [Real.sin_pi_div_four]
  rw [h10, h11]
  field_simp
  <;> ring_nf <;> simp [Real.sqrt_sq] <;> ring_nf <;> norm_num
  <;> ring