import Mathlib

theorem algebra_163233 (α : Real) :
    6 * (Real.sin (2 * α))^2 - 1 - Real.cos (4 * α) =
    -8 * Real.cos (2 * α + Real.pi / 3) * Real.cos (2 * α - Real.pi / 3) := by
  have h1 : Real.cos (4 * α) = 1 - 2 * (Real.sin (2 * α))^2 := by
    have h2 : 4 * α = 2 * (2 * α) := by ring
    rw [h2]
    have h3 : Real.cos (2 * (2 * α)) = 1 - 2 * (Real.sin (2 * α))^2 := by
      rw [Real.cos_two_mul]
      rw [Real.sin_sq]
      ring
    exact h3
  rw [h1]
  have eq1 : -8 * Real.cos (2 * α + Real.pi / 3) * Real.cos (2 * α - Real.pi / 3) =
      6 * (Real.sin (2 * α))^2 - 2 * (Real.cos (2 * α))^2 := by
    have h2 : Real.cos (2 * α + Real.pi / 3) = Real.cos (2 * α) * Real.cos (Real.pi / 3) - Real.sin (2 * α) * Real.sin (Real.pi / 3) := by 
      rw [Real.cos_add]
    have h3 : Real.cos (2 * α - Real.pi / 3) = Real.cos (2 * α) * Real.cos (Real.pi / 3) + Real.sin (2 * α) * Real.sin (Real.pi / 3) := by 
      rw [Real.cos_sub]
    rw [h2, h3]
    have h4 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
    have h5 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
    rw [h4, h5]
    have h6 : (Real.sin (2 * α))^2 + (Real.cos (2 * α))^2 = 1 := Real.sin_sq_add_cos_sq (2 * α)
    have h8 : (Real.sqrt 3) ^ 2 = 3 := by
      rw [Real.sq_sqrt]
      linarith
    nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : Real) by norm_num)]
  linarith [eq1, Real.sin_sq_add_cos_sq (2 * α)]