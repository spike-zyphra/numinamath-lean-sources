import Mathlib

theorem algebra_313419 : Real.sin (Real.pi / 18) ^ 2 + Real.cos (2 * Real.pi / 9) ^ 2 + Real.sin (Real.pi / 18) * Real.cos (2 * Real.pi / 9) = 3 / 4 := by
  have h1 : 2 * Real.pi / 9 = Real.pi / 6 + Real.pi / 18 := by 
    ring_nf
  have h2 : Real.cos (2 * Real.pi / 9) = Real.cos (Real.pi / 6 + Real.pi / 18) := by
    rw [h1]
  have h3 : Real.cos (Real.pi / 6 + Real.pi / 18) = Real.cos (Real.pi / 6) * Real.cos (Real.pi / 18) - Real.sin (Real.pi / 6) * Real.sin (Real.pi / 18) := by 
    rw [Real.cos_add]
  have h4 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
  have h5 : Real.sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
  have eq1 : Real.cos (2 * Real.pi / 9) = Real.sqrt 3 / 2 * Real.cos (Real.pi / 18) - 1 / 2 * Real.sin (Real.pi / 18) := by
    rw [h2, h3, h4, h5]
    <;> ring
  rw [eq1]
  have h6 : Real.sin (Real.pi / 18) ^ 2 + (Real.sqrt 3 / 2 * Real.cos (Real.pi / 18) - 1 / 2 * Real.sin (Real.pi / 18)) ^ 2 + Real.sin (Real.pi / 18) * (Real.sqrt 3 / 2 * Real.cos (Real.pi / 18) - 1 / 2 * Real.sin (Real.pi / 18)) = 3 / 4 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 18), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  linarith