import Mathlib
open Polynomial

theorem algebra_12 {x : ℝ} (hx : x = Real.cos (Real.pi/12)) :
    (16*x^4 - 16*x^2 + 1 : ℝ) = 0 := by
  have h1 : x = Real.cos (Real.pi / 12) := by
    exact hx
  have h2 : Real.cos (Real.pi / 12) = (Real.sqrt 6 + Real.sqrt 2) / 4 := by
    have h3 : Real.cos (Real.pi / 12) = Real.cos (Real.pi / 4 - Real.pi / 6) := by
      ring_nf
    rw [h3]
    rw [Real.cos_sub]
    have h4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    have h5 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    have h6 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
      rw [Real.cos_pi_div_six]
    have h7 : Real.sin (Real.pi / 6) = 1 / 2 := by
      rw [Real.sin_pi_div_six]
    rw [h4, h5, h6, h7]
    have h8 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
      rw [← Real.sqrt_mul (by norm_num)]
      all_goals norm_num
    nlinarith [h8, Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (2 : ℝ)]
  rw [h1, h2]
  nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 6 - Real.sqrt 2), sq_nonneg (Real.sqrt 6 - 2 * Real.sqrt 2), sq_nonneg (Real.sqrt 6 + Real.sqrt 2 - 2 * Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]