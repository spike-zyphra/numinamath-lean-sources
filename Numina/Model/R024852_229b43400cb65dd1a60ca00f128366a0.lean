import Mathlib

theorem algebra_48362 : Real.cos (2 * Real.pi / 5) + Real.cos (4 * Real.pi / 5) = -1 / 2 := by
  have h1 : Real.cos (4 * Real.pi / 5) = - Real.cos (Real.pi / 5) := by
    have h2 : 4 * Real.pi / 5 = Real.pi - Real.pi / 5 := by 
      linarith [Real.pi_pos]
    rw [h2]
    have h3 : Real.cos (Real.pi - Real.pi / 5) = - Real.cos (Real.pi / 5) := by 
      rw [Real.cos_pi_sub]
    exact h3
  have h2 : Real.cos (2 * Real.pi / 5) = 2 * (Real.cos (Real.pi / 5)) ^ 2 - 1 := by
    have h3 : 2 * Real.pi / 5 = 2 * (Real.pi / 5) := by 
      ring
    rw [h3]
    rw [Real.cos_two_mul]
  have h3 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
    have h5 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
      rw [Real.cos_pi_div_five]
    exact h5
  rw [h1, h2, h3]
  nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]