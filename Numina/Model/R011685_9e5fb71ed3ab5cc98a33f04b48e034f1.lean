import Mathlib

theorem algebra_285016 (α : ℝ) (hα : α = Real.pi / 9) :
    Real.cos α + Real.cos (3 * α) + Real.cos (5 * α) + Real.cos (7 * α) = 1 / 2 := by
  rw [hα]
  have h2 : Real.cos (3 * (Real.pi / 9)) = 1 / 2 := by
    have h3 : 3 * (Real.pi / 9) = Real.pi / 3 := by
      ring
    rw [h3] 
    exact Real.cos_pi_div_three 
  have h3 : Real.cos (5 * (Real.pi / 9)) = - Real.cos (4 * (Real.pi / 9)) := by
    have h4 : 5 * (Real.pi / 9) = Real.pi - 4 * (Real.pi / 9) := by 
      linarith [Real.pi_pos] 
    rw [h4] 
    rw [Real.cos_pi_sub] 
  have h4 : Real.cos (7 * (Real.pi / 9)) = - Real.cos (2 * (Real.pi / 9)) := by
    have h7 : 7 * (Real.pi / 9) = Real.pi - 2 * (Real.pi / 9) := by 
      linarith [Real.pi_pos] 
    rw [h7] 
    rw [Real.cos_pi_sub] 
  rw [h2, h3, h4]
  have h5 : Real.cos (4 * (Real.pi / 9)) + Real.cos (2 * (Real.pi / 9)) = Real.cos (Real.pi / 9) := by 
    have h7 : Real.cos (4 * (Real.pi / 9)) + Real.cos (2 * (Real.pi / 9)) = 2 * Real.cos (3 * (Real.pi / 9)) * Real.cos (Real.pi / 9) := by
      have h8 : 4 * (Real.pi / 9) = 3 * (Real.pi / 9) + (Real.pi / 9) := by ring
      have h9 : 2 * (Real.pi / 9) = 3 * (Real.pi / 9) - (Real.pi / 9) := by ring
      rw [h8, h9]
      have hcos : Real.cos (3 * (Real.pi / 9) + (Real.pi / 9)) + Real.cos (3 * (Real.pi / 9) - (Real.pi / 9)) = 2 * Real.cos (3 * (Real.pi / 9)) * Real.cos (Real.pi / 9) := by 
        rw [Real.cos_add, Real.cos_sub]
        ring
      linarith [hcos]
    rw [h7, h2]
    all_goals linarith
  linarith [h5]