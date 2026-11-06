import Mathlib

theorem algebra_101584 : Real.cos (Real.pi / 5) - Real.cos (2 * Real.pi / 5) = 1 / 2 := by
  have h1 : Real.cos (2 * Real.pi / 5) = 2 * (Real.cos (Real.pi / 5)) ^ 2 - 1 := by 
    have h2 : 2 * Real.pi / 5 = 2 * (Real.pi / 5) := by 
      ring
    rw [h2]
    rw [Real.cos_two_mul]
  have h2 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
    have hcos : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
      rw [Real.cos_pi_div_five]
    exact hcos
  rw [h1, h2]
  nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_nonneg ((1 + Real.sqrt 5) / 4 - (1 : ℝ)) ]