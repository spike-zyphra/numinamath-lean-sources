import Mathlib

theorem algebra_161807 (α : ℝ) :
    1 - Real.cos (2 * α - Real.pi) + Real.cos (4 * α - 2 * Real.pi) =
    4 * Real.cos (2 * α) * Real.cos (Real.pi / 6 + α) * Real.cos (Real.pi / 6 - α) := by
  have h1 : Real.cos (2 * α - Real.pi) = - Real.cos (2 * α) := by 
    have h2 : 2 * α - Real.pi = 2 * α - Real.pi := rfl
    rw [show 2 * α - Real.pi = (2 * α) - Real.pi by ring]
    rw [Real.cos_sub_pi]
  
  have h2 : Real.cos (4 * α - 2 * Real.pi) = Real.cos (4 * α) := by 
    have h2 : 4 * α - 2 * Real.pi = 4 * α - 2 * Real.pi := rfl
    rw [show 4 * α - 2 * Real.pi = (4 * α) - (2 * Real.pi) by ring]
    rw [Real.cos_sub_two_pi]
  
  have h3 : Real.cos (4 * α) = 2 * (Real.cos (2 * α))^2 - 1 := by 
    have h : Real.cos (4 * α) = 2 * (Real.cos (2 * α))^2 - 1 := by 
      rw [show 4 * α = 2 * (2 * α) by ring]
      rw [Real.cos_two_mul]
      <;> ring 
    linarith
  
  have h4 : Real.cos (Real.pi / 6 + α) = Real.cos (Real.pi / 6) * Real.cos α - Real.sin (Real.pi / 6) * Real.sin α := by
    rw [Real.cos_add]
  
  have h5 : Real.cos (Real.pi / 6 - α) = Real.cos (Real.pi / 6) * Real.cos α + Real.sin (Real.pi / 6) * Real.sin α := by 
    rw [Real.cos_sub]
  
  have h6 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
  
  have h7 : Real.sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
  
  rw [h1, h2, h3]
  rw [h4, h5, h6, h7]
  have h8 : Real.sin α ^2 = 1 - Real.cos α ^2 := by 
    have h9 : Real.sin α ^2 + Real.cos α ^2 = 1 := Real.sin_sq_add_cos_sq α
    linarith
  
  have h9 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by 
    rw [Real.cos_two_mul]
    <;> ring
  
  simp only [h9]
  ring_nf
  <;> simp [Real.sin_sq, h8]
  <;> nlinarith [sq_nonneg (Real.cos α ^ 2 - 1 / 4), sq_nonneg (Real.sin α ^ 2 - 1 / 4)]