import Mathlib

theorem algebra_186004 (α : ℝ) : Real.sin ((5 / 2) * Real.pi - 2 * α) + 2 * (Real.sin (2 * α - 3 / 2 * Real.pi))^2 - 1 = 2 * Real.cos α * Real.cos (3 * α) := by

  have h1 : Real.sin ((5 / 2) * Real.pi - 2 * α) = Real.cos (2 * α) := by 
    have h3 : (5 / 2) * Real.pi - 2 * α = Real.pi / 2 - 2 * α + 2 * Real.pi := by
      linarith [Real.pi_pos]
    rw [h3]
    have h4 : Real.sin (Real.pi / 2 - 2 * α + 2 * Real.pi) = Real.cos (2 * α) := by
      have h5 : Real.sin (Real.pi / 2 - 2 * α + 2 * Real.pi) = Real.sin (Real.pi / 2 - 2 * α) := by 
        rw [show Real.pi / 2 - 2 * α + 2 * Real.pi = (Real.pi / 2 - 2 * α) + 2 * Real.pi by ring]
        rw [Real.sin_add_two_pi]
      rw [h5]
      have h8 : Real.sin (Real.pi / 2 - 2 * α) = Real.cos (2 * α) := by
        have h9 : Real.sin (Real.pi / 2 - 2 * α) = Real.cos (2 * α) := by 
          rw [show Real.pi / 2 - 2 * α = Real.pi / 2 - (2 * α) by ring]
          rw [Real.sin_pi_div_two_sub]
        exact h9
      exact h8
    exact h4

  have h2 : Real.sin (2 * α - 3 / 2 * Real.pi) = Real.cos (2 * α) := by
    have h3 : 2 * α - 3 / 2 * Real.pi = (2 * α - Real.pi / 2) - Real.pi := by
      linarith [Real.pi_pos]
    rw [h3]
    have h4 : Real.sin ((2 * α - Real.pi / 2) - Real.pi) = Real.cos (2 * α) := by
      have h5 : Real.sin ((2 * α - Real.pi / 2) - Real.pi) = - Real.sin (2 * α - Real.pi / 2) := by 
        rw [show (2 * α - Real.pi / 2) - Real.pi = (2 * α - Real.pi / 2) - Real.pi by ring]
        rw [Real.sin_sub, Real.sin_pi, Real.cos_pi]
        all_goals ring
      rw [h5]
      have h6 : Real.sin (2 * α - Real.pi / 2) = - Real.cos (2 * α) := by
        rw [show 2 * α - Real.pi / 2 = 2 * α - Real.pi / 2 by ring]
        rw [Real.sin_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]
        all_goals ring
      rw [h6]
      all_goals ring
    exact h4

  have eq1 : Real.sin ((5 / 2) * Real.pi - 2 * α) + 2 * (Real.sin (2 * α - 3 / 2 * Real.pi))^2 - 1 = Real.cos (2 * α) + 2 * Real.cos (2 * α)^2 - 1 := by 
    rw [h1, h2]
    all_goals ring

  have eq2 : Real.cos (2 * α) + 2 * Real.cos (2 * α)^2 - 1 = 2 * Real.cos α * Real.cos (3 * α) := by 
    have hcos1 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by 
      rw [Real.cos_two_mul]
    have hcos2 : Real.cos (3 * α) = 4 * Real.cos α ^ 3 - 3 * Real.cos α := by 
      rw [Real.cos_three_mul]
    rw [hcos1, hcos2]
    nlinarith [Real.cos_sq_add_sin_sq α, sq_nonneg (Real.cos α ^ 2 - 1), sq_nonneg (Real.cos α ^ 2 - 3 / 4)]

  rw [eq1, eq2]