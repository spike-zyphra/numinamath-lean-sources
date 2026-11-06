import Mathlib

theorem algebra_189414 : Real.cos (2/5 * Real.pi) + Real.cos (4/5 * Real.pi) = -1/2 := by

  have h1 : Real.cos (4/5 * Real.pi) = - Real.cos (Real.pi / 5) := by
    have h1 : 4/5 * Real.pi = Real.pi - Real.pi / 5 := by
      ring
    rw [h1]
    rw [Real.cos_pi_sub]

  have h2 : Real.cos (2/5 * Real.pi) = 2 * (Real.cos (Real.pi / 5))^2 - 1 := by
    have h2 : 2/5 * Real.pi = 2 * (Real.pi / 5) := by
      ring
    rw [h2]
    have h3 : Real.cos (2 * (Real.pi / 5)) = 2 * (Real.cos (Real.pi / 5))^2 - 1 := by
      rw [Real.cos_two_mul]
    exact h3

  have h3 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
    rw [Real.cos_pi_div_five]

  rw [h1, h2, h3]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num : (0 : ℝ) < 5), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num : (0 : ℝ) ≤ 5), sq_nonneg (Real.sqrt 5 - 1)]