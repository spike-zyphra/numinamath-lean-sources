import Mathlib

theorem algebra_162715 (α : ℝ) :
    4 * Real.cos (α - Real.pi / 2) * (Real.sin (Real.pi / 2 + α))^3 -
    4 * Real.sin (5 * Real.pi / 2 - α) * (Real.cos (3 * Real.pi / 2 + α))^3 =
    Real.sin (4 * α) := by
  have h1 : Real.cos (α - Real.pi / 2) = Real.sin α := by 
    rw [show α - Real.pi / 2 = α - Real.pi / 2 by rfl]
    rw [Real.cos_sub]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  have h2 : Real.sin (Real.pi / 2 + α) = Real.cos α := by 
    rw [show Real.pi / 2 + α = Real.pi / 2 + α by rfl]
    rw [Real.sin_add]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  have h3 : Real.sin (5 * Real.pi / 2 - α) = Real.cos α := by
    have h31 : 5 * Real.pi / 2 - α = Real.pi / 2 - α + 2 * Real.pi := by 
      linarith [Real.pi_pos]
    rw [h31]
    have h32 : Real.sin (Real.pi / 2 - α + 2 * Real.pi) = Real.sin (Real.pi / 2 - α) := by 
      rw [show Real.pi / 2 - α + 2 * Real.pi = (Real.pi / 2 - α) + 2 * Real.pi by ring]
      rw [Real.sin_add_two_pi]
    rw [h32]
    have h33 : Real.sin (Real.pi / 2 - α) = Real.cos α := by 
      rw [show Real.pi / 2 - α = Real.pi / 2 - α by rfl]
      rw [Real.sin_sub]
      simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
    rw [h33]
  have h4 : Real.cos (3 * Real.pi / 2 + α) = Real.sin α := by 
    have h41 : 3 * Real.pi / 2 + α = Real.pi + (Real.pi / 2 + α) := by 
      linarith [Real.pi_pos]
    rw [h41]
    have h42 : Real.cos (Real.pi + (Real.pi / 2 + α)) = - Real.cos (Real.pi / 2 + α) := by 
      rw [show Real.pi + (Real.pi / 2 + α) = Real.pi + (Real.pi / 2 + α) by rfl]
      rw [Real.cos_add]
      simp [Real.cos_pi, Real.sin_pi]
    rw [h42]
    have h43 : Real.cos (Real.pi / 2 + α) = - Real.sin α := by 
      rw [show Real.pi / 2 + α = Real.pi / 2 + α by rfl]
      rw [Real.cos_add]
      simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
    rw [h43]
    all_goals ring_nf 
  rw [h1, h2, h3, h4]
  -- Now simplify the expression with substitutions
  -- First term: 4 * sin(α) * cos^3(α)
  -- Second term: 4 * cos(α) * sin^3(α)
  -- Difference: 4 * sin(α) * cos(α) * (cos^2(α) - sin^2(α)) = sin(4α)
  have h5 : 4 * Real.sin α * (Real.cos α)^3 - 4 * Real.cos α * (Real.sin α)^3 = 4 * Real.sin α * Real.cos α * (Real.cos α ^ 2 - Real.sin α ^ 2) := by 
    ring
  have eq2 : 4 * Real.sin α * Real.cos α * (Real.cos α ^ 2 - Real.sin α ^ 2) = Real.sin (4 * α) := by
    have eq3 : Real.sin (4 * α) = 2 * Real.sin (2 * α) * Real.cos (2 * α) := by 
      rw [show 4 * α = 2 * (2 * α) by ring]
      rw [Real.sin_two_mul]
    have eq4 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by 
      rw [show 2 * α = 2 * α by ring]
      rw [Real.sin_two_mul]
    have eq5 : Real.cos (2 * α) = Real.cos α ^ 2 - Real.sin α ^ 2 := by 
      rw [show 2 * α = 2 * α by ring]
      rw [Real.cos_two_mul]
      rw [Real.sin_sq, Real.cos_sq]
      ring_nf
    rw [eq3, eq4, eq5]
    ring_nf
  linarith [h5, eq2]