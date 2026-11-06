import Mathlib

open Real Set
open scoped Real

theorem algebra_10266 {θ : ℝ} (h : sin (π/6 - θ) = cos (π/6 + θ)) :
    cos (2*θ) = 0 := by
  have h1 : sin (π / 6 - θ) = sin (π / 6) * cos θ - cos (π / 6) * sin θ := by
    rw [sin_sub]
  have h2 : cos (π / 6 + θ) = cos (π / 6) * cos θ - sin (π / 6) * sin θ := by
    rw [cos_add]
  have h3 : sin (π / 6) = 1 / 2 := by
    rw [sin_pi_div_six]
  have h4 : cos (π / 6) = Real.sqrt 3 / 2 := by
    rw [cos_pi_div_six]
  rw [h1, h2, h3, h4] at h
  have h5 : (1 / 2) * cos θ - (Real.sqrt 3 / 2) * sin θ = (Real.sqrt 3 / 2) * cos θ - (1 / 2) * sin θ := by
    linarith
  have h6 : (cos θ + sin θ) * (1 / 2 - Real.sqrt 3 / 2) = 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  cases' (mul_eq_zero.1 h6) with h7 h8
  · -- Case cos θ + sin θ = 0
    have h8 : sin θ = -cos θ := by
      linarith
    have h9 : cos (2 * θ) = 0 := by
      have h10 : cos (2 * θ) = cos θ ^ 2 - sin θ ^ 2 := by
        rw [cos_two_mul, sin_sq]
        all_goals ring
      rw [h10]
      rw [show sin θ = -cos θ by linarith [h8]]
      have h11 : cos θ ^ 2 - (-cos θ) ^ 2 = 0 := by
        ring_nf
      linarith [h11]
    linarith
  · -- Case 1 / 2 - Real.sqrt 3 / 2 = 0
    have h9 : (1 / 2 : ℝ) - Real.sqrt 3 / 2 = 0 := by
      linarith
    have h10 : Real.sqrt 3 = 1 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ 3)]
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]